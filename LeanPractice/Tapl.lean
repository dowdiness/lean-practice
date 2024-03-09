namespace Bool

inductive Term where
  | True | False | If (t1 t2 t3: Term)
  deriving Repr

#eval Term.If .False .True .False

inductive eval1 : Term -> Term -> Prop where
  | E_ifTrue {t2 t3 : Term} : eval1 (.If .True t2 t3) t2
  | E_ifFalse {t2 t3 : Term} : eval1 (.If .False t2 t3) t3
  | E_if {t1 t1' t2 t3} : eval1 t1 t1' -> eval1 (.If t1 t2 t3) (.If t1' t2 t3)
infix:50 " ⟶ " => eval1

example : .If .True .True .False ⟶ .True := by apply eval1.E_ifTrue

theorem eval1_deterministic : t ⟶ t' -> t ⟶ t'' -> t' = t'' := by
  intro t_t' t_t''
  revert t''

  induction t_t'
  case E_ifTrue =>
    intro t'' t_t''
    cases t_t'' with
    | E_if => contradiction
    | E_ifTrue => rfl
  case E_ifFalse =>
    intro t'' t_t''
    cases t_t'' with
    | E_if => contradiction
    | E_ifFalse => rfl
  case E_if t1 t1' t2 t3 t1_t1' ind_h =>
    intro t'' t_t''
    cases t_t'' with
    | E_ifTrue => contradiction
    | E_ifFalse => contradiction
    | E_if =>
      rename_i t1'' t1_t1''
      have : t1' = t1'' := ind_h t1_t1''
      rw[this]

@[simp] def isValue (t: Term) : Prop := t = Term.True ∨ t = Term.False

-- p.28 定義3.5.6. 正規形
def isNormalForm (t: Term) : Prop := ¬ (∃ t', t ⟶ t')

theorem trueIsNF : isNormalForm .True := by
  unfold isNormalForm
  intro true_t'
  have ⟨t', true_t'⟩ := true_t'
  contradiction

theorem falseIsNF : isNormalForm .False := by
  intro false_t'
  have ⟨t', false_t' ⟩ := false_t'
  contradiction

-- 補題: 「t は値である」 か 「t は値でない」 のどちらかが必ず成り立つ
theorem isValueOrNotValue (t: Term) : isValue t ∨ ¬ isValue t := by
  cases t
  case True =>
    apply Or.intro_left
    unfold isValue
    simp
  case False =>
    apply Or.intro_left
    unfold isValue
    apply Or.intro_right
    rfl
  case If =>
    apply Or.intro_right
    unfold isValue
    intro h
    cases h
    case h.inl h => contradiction
    case h.inr h => contradiction

-- 補題: t が値でないならば、 t = if t1 then t2 else t3 が成り立つ
theorem tIsIf_when_tIsNotVal {t: Term} (tIsNotVal : ¬ isValue t) : ∃ t1 t2 t3, t = .If t1 t2 t3 := by
  cases t
  case True =>
    have : isValue .True := by simp
    contradiction
  case False =>
    have : isValue .False := by simp
    contradiction
  case If t1 t2 t3 =>
    exists t1; exists t2; exists t3;

-- example : (t: Term) isValue t -> isNormalForm t := by
  -- done

-- example : (t: Term) : isNormalForm t -> isValue t := by
  -- done

-- 3.5.7 and 3.5.8
theorem value_normalform (t: Term) : isValue t ↔ isNormalForm t := by
  apply Iff.intro
  case mp =>
    intro tIsVal
    intro ex_t'
    have ⟨t', t_t'⟩ := ex_t'
    cases tIsVal
    case inl h =>
      rw [h] at t_t'
      contradiction
    case inr h =>
      rw [h] at t_t'
      contradiction
  case mpr =>
    intro tIsNF
    have tIsValOrNotVal := isValueOrNotValue t
    cases tIsValOrNotVal
    case inl => trivial
    case inr tIsNotVal =>
      have tIsNotNF: ∃ t', t ⟶ t' := by
        have ⟨t1, ⟨t2, ⟨t3, tIsIf⟩⟩⟩ := tIsIf_when_tIsNotVal tIsNotVal
        clear tIsNF tIsNotVal; revert t t2 t3;
        induction t1
        case True =>
          intro t t2 t3 tIsIf
          exists t2
          rewrite[tIsIf]
          apply eval1.E_ifTrue
        case False =>
          intro t t2 t3 tIsIf
          exists t3
          rewrite[tIsIf]
          apply eval1.E_ifFalse
        case If =>
          intro t t2 t3 tIsIf
          rename_i t1_1 t2_2 t3_3 ind_h _ _
          let t1 : Term := .If t1_1 t2_2 t3_3
          have t1IsIf: t1 = (.If t1_1 t2_2 t3_3) := by simp
          let ⟨t1', t1_t1'⟩ := ind_h t1 t2_2 t3_3 t1IsIf
          exists (.If t1' t2 t3)
          rewrite [tIsIf]
          apply eval1.E_if
          exact t1_t1'
      contradiction
