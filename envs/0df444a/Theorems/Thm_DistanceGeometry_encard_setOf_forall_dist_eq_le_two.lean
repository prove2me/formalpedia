-- Prove2me | Theorems.Thm_DistanceGeometry_encard_setOf_forall_dist_eq_le_two
-- name    : DistanceGeometry.encard_setOf_forall_dist_eq_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:24.74924+00:00
-- url     : https://prove2.me/theorems/b8a3afca-58c3-47e2-bf85-b3352c22a0b5
-- title:
--   Distance Geometry: encard set Of forall dist eq le two
-- statement:
--   If the orthogonal complement of the center span is one-dimensional (the centers
--   span a hyperplane), the intersection of the spheres `{p | ∀ i, dist p (c i) = r i}`
--   has at most two elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Trilateration.lean#L160-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Trilateration.lean#L160-L169

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
public import Definitions.Def_LeanPool_DistanceGeometry_Trilateration
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
  {ι : Type*} {c : ι → P} {r : ι → ℝ}

theorem DistanceGeometry.encard_setOf_forall_dist_eq_le_two [Nonempty ι]
    (hc : finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1) (r : ι → ℝ) :
    Set.encard {p : P | ∀ i, dist p (c i) = r i} ≤ 2 := by sorry
