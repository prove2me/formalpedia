-- Prove2me | Theorems.Thm_DeciSigma1_decideDisjEntailsTopFreeFin_correct
-- name    : DeciSigma1.decideDisjEntailsTopFreeFin_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T15:26:50.269131+00:00
-- url     : https://prove2.me/theorems/7faf6f2a-49f0-4d94-88e9-d788dacbbaa1
-- title:
--   Deci Sigma1: decide Disj Entails Top Free Fin correct
-- statement:
--   `decideDisjEntailsTopFreeFin` returns `true` exactly when the entailment holds over finite
--   trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L319-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Main.lean#L319-L322

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

theorem DeciSigma1.decideDisjEntailsTopFreeFin_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeFin Γ q) = true ↔ DisjEntailsTopFreeFin Γ q := by sorry
