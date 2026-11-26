-- Prove2me | Theorems.Thm_Auto_aux_exists_wienerEnvelope_comp_injective_continuousLinearMap_bound
-- name    : Auto.aux_exists_wienerEnvelope_comp_injective_continuousLinearMap_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:45.94344+00:00
-- url     : https://prove2.me/theorems/a549df06-5573-5464-b5c1-53fee2c8ef8c
-- title:
--   Auto: aux exists wiener Envelope comp injective continuous Linear Map bound
-- statement:
--   The quantitative form of injective pullback.  Its positive constant is obtained by
--   straightening the range of the map, applying the uniform slice estimate, and changing
--   coordinates on the source.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1727-L1802
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L1727-L1802

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_exists_wienerEnvelope_comp_injective_continuousLinearMap_bound
    {k n : ℕ} {K : Type*} [NormedAddCommGroup K]
    (π : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → K, MemW0 f →
      (∫ x, wienerEnvelope (f ∘ π) 1 x) ≤ C * ∫ y, wienerEnvelope f 1 y := by sorry
