-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_LowerAt_trans_right
-- name    : DeciSigma1.Constraints.LowerAt.trans_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:22.615095+00:00
-- url     : https://prove2.me/theorems/38700ac8-35df-4b3f-aa11-0c43cb92bb0a
-- title:
--   Lower At: trans right
-- statement:
--   The Lower At construction uses the trans right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L400-L404
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L400-L404

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

theorem DeciSigma1.Constraints.LowerAt.trans_right {π : List (Fin n)} {x y z : V}
    (h : LowerAt Γ π x y) (hyz : Derives Γ y z) : LowerAt Γ π x z := by sorry
