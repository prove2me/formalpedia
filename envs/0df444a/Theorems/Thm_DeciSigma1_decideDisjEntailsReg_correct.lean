-- Prove2me | Theorems.Thm_DeciSigma1_decideDisjEntailsReg_correct
-- name    : DeciSigma1.decideDisjEntailsReg_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:24:48.445857+00:00
-- url     : https://prove2.me/theorems/6d139754-6103-4d27-85e0-fd17551e802e
-- title:
--   Deci Sigma1: decide Disj Entails Reg correct
-- statement:
--   `decideDisjEntailsReg` returns `true` exactly when the entailment holds over regular
--   trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L246-L249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L246-L249

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

theorem DeciSigma1.decideDisjEntailsReg_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsReg c Γ q) = true ↔ DisjEntailsReg c Γ q := by sorry
