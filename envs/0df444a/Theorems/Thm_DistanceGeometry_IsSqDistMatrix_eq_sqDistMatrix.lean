-- Prove2me | Theorems.Thm_DistanceGeometry_IsSqDistMatrix_eq_sqDistMatrix
-- name    : DistanceGeometry.IsSqDistMatrix.eq_sqDistMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:25.251524+00:00
-- url     : https://prove2.me/theorems/90caf9e1-d0d1-4b65-914b-47fac2a8d0e7
-- title:
--   Is Sq Dist Matrix: eq sq Dist Matrix
-- statement:
--   The Is Sq Dist Matrix construction uses the eq sq Dist Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L72-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L72-L75

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.IsSqDistMatrix.eq_sqDistMatrix {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) :
    D = sqDistMatrix x := by sorry
