-- Prove2me | Theorems.Thm_DistanceGeometry_posSemidef_centeredGram
-- name    : DistanceGeometry.posSemidef_centeredGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:42.18398+00:00
-- url     : https://prove2.me/theorems/65d3dbba-f2fc-421f-b221-dd11256192b7
-- title:
--   Distance Geometry: pos Semidef centered Gram
-- statement:
--   The basepoint-centered Gram matrix of a squared-distance matrix is positive semidefinite.
--   This is the positive-semidefiniteness half of Schoenberg's necessary conditions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L78-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Schoenberg.lean#L78-L83

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

theorem DistanceGeometry.posSemidef_centeredGram
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).PosSemidef := by sorry
