-- Prove2me | Theorems.Thm_DistanceGeometry_centeredGram_apply_eq_inner
-- name    : DistanceGeometry.centeredGram_apply_eq_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:40.627454+00:00
-- url     : https://prove2.me/theorems/200b0993-d6a6-46ad-b66c-24780a460d00
-- title:
--   Distance Geometry: centered Gram apply eq inner
-- statement:
--   The polarization identity. When `D` is the squared-distance matrix of `x`, the
--   `(i, j)` entry of the basepoint-centered Gram matrix is the inner product of the recentred
--   vectors `x i - x 0` and `x j - x 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L53-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L53-L66

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

theorem DistanceGeometry.centeredGram_apply_eq_inner
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) (i j : Fin n) :
    centeredGram D i j = ⟪x i - x 0, x j - x 0⟫ := by sorry
