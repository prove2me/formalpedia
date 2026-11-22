-- Prove2me | Theorems.Thm_DistanceGeometry_centeredGram_eq_gram
-- name    : DistanceGeometry.centeredGram_eq_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:43.143386+00:00
-- url     : https://prove2.me/theorems/a5f55a65-e26e-4083-95fa-55300c4e2005
-- title:
--   Distance Geometry: centered Gram eq gram
-- statement:
--   The basepoint-centered Gram matrix is the Gram matrix of the recentred vectors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L69-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L69-L74

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

theorem DistanceGeometry.centeredGram_eq_gram
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    centeredGram D = gram ℝ (fun i => x i - x 0) := by sorry
