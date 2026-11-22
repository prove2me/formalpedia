-- Prove2me | Theorems.Thm_DistanceGeometry_schoenberg_easy
-- name    : DistanceGeometry.schoenberg_easy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:43.211398+00:00
-- url     : https://prove2.me/theorems/91018d77-97c5-4556-81c5-d6fd8081cf0f
-- title:
--   Distance Geometry: schoenberg easy
-- statement:
--   The necessary conditions in Schoenberg's theorem: the basepoint-centered Gram matrix of a
--   squared-distance matrix of a configuration in `EuclideanSpace ℝ (Fin k)` is positive
--   semidefinite and has rank at most `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L105-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L105-L109

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]

theorem DistanceGeometry.schoenberg_easy
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).PosSemidef ∧ (centeredGram D).rank ≤ k := by sorry
