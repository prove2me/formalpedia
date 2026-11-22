-- Prove2me | Theorems.Thm_DeciSigma1_decideDisjEntailsTopFree_correct
-- name    : DeciSigma1.decideDisjEntailsTopFree_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:26:12.923058+00:00
-- url     : https://prove2.me/theorems/753c0732-1985-45a1-a96c-cd3c3f5b05ef
-- title:
--   Deci Sigma1: decide Disj Entails Top Free correct
-- statement:
--   `decideDisjEntailsTopFree` returns `true` exactly when the entailment holds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L295-L298
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L295-L298

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

theorem DeciSigma1.decideDisjEntailsTopFree_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFree Γ q) = true ↔ DisjEntailsTopFree Γ q := by sorry
