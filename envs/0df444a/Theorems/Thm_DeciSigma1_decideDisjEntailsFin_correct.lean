-- Prove2me | Theorems.Thm_DeciSigma1_decideDisjEntailsFin_correct
-- name    : DeciSigma1.decideDisjEntailsFin_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:25:13.392795+00:00
-- url     : https://prove2.me/theorems/1ae16851-721b-4615-ba56-8a3cf065e7ec
-- title:
--   Deci Sigma1: decide Disj Entails Fin correct
-- statement:
--   `decideDisjEntailsFin` returns `true` exactly when the entailment holds over finite
--   trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L258-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L258-L261

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

theorem DeciSigma1.decideDisjEntailsFin_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsFin c Γ q) = true ↔ DisjEntailsFin c Γ q := by sorry
