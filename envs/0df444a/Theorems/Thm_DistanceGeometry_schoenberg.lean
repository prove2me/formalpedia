-- Prove2me | Theorems.Thm_DistanceGeometry_schoenberg
-- name    : DistanceGeometry.schoenberg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:11.332985+00:00
-- url     : https://prove2.me/theorems/554a8d78-daaf-4e68-9988-953dee214ba4
-- title:
--   Distance Geometry: schoenberg
-- statement:
--   Schoenberg's characterization of Euclidean squared-distance matrices. A matrix
--   `D` satisfying this project's `IsPreDistMatrix` predicate (symmetric and hollow)
--   embeds as a squared-distance matrix in `EuclideanSpace ℝ (Fin k)` if and only if its
--   basepoint-centered Gram matrix is positive semidefinite and has rank at most `k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean#L235-L241
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean#L235-L241

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
set_option autoImplicit true
@[expose] public section
public section
open Matrix
open scoped RealInnerProductSpace
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]

theorem DistanceGeometry.schoenberg {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D) :
    EmbedsIn D k ↔ (centeredGram D).PosSemidef ∧ (centeredGram D).rank ≤ k := by sorry
