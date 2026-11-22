-- Prove2me | Theorems.Thm_DeciSigma1_decideDisjEntailsTopFreeReg_correct
-- name    : DeciSigma1.decideDisjEntailsTopFreeReg_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:25:37.151937+00:00
-- url     : https://prove2.me/theorems/313c95d0-ca13-4c20-9057-810bfb200e45
-- title:
--   Deci Sigma1: decide Disj Entails Top Free Reg correct
-- statement:
--   `decideDisjEntailsTopFreeReg` returns `true` exactly when the entailment holds over
--   regular trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L307-L310
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L307-L310

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
variable {n : ℕ} {V : Type}
variable [Fintype V] [DecidableEq V] {k : ℕ}

theorem DeciSigma1.decideDisjEntailsTopFreeReg_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeReg Γ q) = true ↔ DisjEntailsTopFreeReg Γ q := by sorry
