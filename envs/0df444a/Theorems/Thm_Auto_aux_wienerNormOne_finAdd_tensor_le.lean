-- Prove2me | Theorems.Thm_Auto_aux_wienerNormOne_finAdd_tensor_le
-- name    : Auto.aux_wienerNormOne_finAdd_tensor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:55:09.012128+00:00
-- url     : https://prove2.me/theorems/91ae66ca-20fa-4bf3-8a09-8a61186c8e6e
-- title:
--   Auto: aux wiener Norm One fin Add tensor le
-- statement:
--   The Euclidean-coordinate tensor product obeys the same Wiener-integral estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2497-L2522
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2497-L2522

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_wienerNormOne_finAdd_tensor_le {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : Continuous f) (hg : Continuous g) :
    wienerNormOne (fun z : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd z).1 * g (EuclideanSpace.finAddEquivProd z).2) ≤
      wienerNormOne f * wienerNormOne g := by sorry
