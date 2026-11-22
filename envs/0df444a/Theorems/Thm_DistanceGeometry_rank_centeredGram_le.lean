-- Prove2me | Theorems.Thm_DistanceGeometry_rank_centeredGram_le
-- name    : DistanceGeometry.rank_centeredGram_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:46.335259+00:00
-- url     : https://prove2.me/theorems/e93857af-e1f9-4fb3-b28f-3e6ecb14a7c3
-- title:
--   Distance Geometry: rank centered Gram le
-- statement:
--   The basepoint-centered Gram matrix of a squared-distance matrix of a configuration in
--   dimension `k` has rank at most `k`. This is the rank half of Schoenberg's necessary
--   conditions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L88-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L88-L100

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

theorem DistanceGeometry.rank_centeredGram_le
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).rank ≤ k := by sorry
