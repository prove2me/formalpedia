-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_UpperAt_trans_left
-- name    : DeciSigma1.Constraints.UpperAt.trans_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:19.822469+00:00
-- url     : https://prove2.me/theorems/b9173d40-b900-43af-b7f7-b5df2c723596
-- title:
--   Upper At: trans left
-- statement:
--   The Upper At construction uses the trans left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L406-L410
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L406-L410

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Constraints.UpperAt.trans_left {π : List (Fin n)} {x y z : V}
    (hxy : Derives Γ x y) (h : UpperAt Γ π y z) : UpperAt Γ π x z := by sorry
