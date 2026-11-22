-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_iteratedLift_basis_eq
-- name    : BooleanIsoperimetry.CoherentGap.iteratedLift_basis_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:18.846466+00:00
-- url     : https://prove2.me/theorems/c52b3ac5-5d35-4867-8ad3-b09e84a87e84
-- title:
--   Coherent Gap: iterated Lift basis eq
-- statement:
--   The Coherent Gap construction uses the iterated Lift basis eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L282-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L282-L324

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.iteratedLift_basis_eq {n : ℕ} (coordinate : Fin n) :
    ∀ {steps : ℕ} (hsteps : 0 < steps),
      iteratedLift (basis coordinate) steps =
        basis (⟨coordinate.val + steps, by omega⟩ : Fin (n + steps)) -
          basis (⟨steps - 1, by omega⟩ : Fin (n + steps))
  := by sorry
