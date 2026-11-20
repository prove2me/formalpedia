-- Prove2me | solution 1 for not_contains_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:14:54.890818+00:00
-- url     : https://prove2.me/submissions/cbe2d16b-50b4-4641-902b-e1486d38403c

module
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Theorems.Thm_contains_refl
public import Theorems.Thm_contains_of_isEmpty
attribute [local refl] contains_refl
attribute [local simp] contains_of_isEmpty

set_option autoImplicit true
@[expose] public section
public section
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}
theorem _root_.solution (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) :
    ¬ Contains P fun (_ : γ) (_ : δ) ↦ False := by simp [Contains, *]
