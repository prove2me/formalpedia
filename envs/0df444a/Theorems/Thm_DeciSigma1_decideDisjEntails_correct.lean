-- Prove2me | Theorems.Thm_DeciSigma1_decideDisjEntails_correct
-- name    : DeciSigma1.decideDisjEntails_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:24:01.107113+00:00
-- url     : https://prove2.me/theorems/45dd1a85-4be8-45d6-a62d-b7a7d8626361
-- title:
--   Deci Sigma1: decide Disj Entails correct
-- statement:
--   `decideDisjEntails` returns `true` exactly when the entailment holds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L235-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L235-L237

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n k : ℕ} {V : Type}
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.decideDisjEntails_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : @decide _ (decideDisjEntails c Γ q) = true ↔ DisjEntails c Γ q := by sorry
