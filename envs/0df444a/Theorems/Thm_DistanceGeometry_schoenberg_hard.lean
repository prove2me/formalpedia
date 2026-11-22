-- Prove2me | Theorems.Thm_DistanceGeometry_schoenberg_hard
-- name    : DistanceGeometry.schoenberg_hard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:12.738763+00:00
-- url     : https://prove2.me/theorems/a620ecf9-e21d-458c-9329-a62ffcb8c56c
-- title:
--   Distance Geometry: schoenberg hard
-- statement:
--   The sufficiency direction of Schoenberg's theorem. If `D` satisfies this project's
--   `IsPreDistMatrix` predicate (symmetric and hollow) and its basepoint-centered Gram
--   matrix is positive semidefinite of rank at most `k`, then `D` is the squared-distance
--   matrix of some configuration in
--   `EuclideanSpace ℝ (Fin k)`.
--
--   This is the converse of `schoenberg_easy`: it reconstructs the point configuration
--   from the Gram data.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean#L197-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/SchoenbergHard.lean#L197-L229

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

theorem DistanceGeometry.schoenberg_hard
    {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPreDistMatrix D)
    (hPSD : (centeredGram D).PosSemidef)
    (hrank : (centeredGram D).rank ≤ k) :
    EmbedsIn D k := by sorry
