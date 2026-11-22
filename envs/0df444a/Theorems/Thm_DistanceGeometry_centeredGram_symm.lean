-- Prove2me | Theorems.Thm_DistanceGeometry_centeredGram_symm
-- name    : DistanceGeometry.centeredGram_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:25.334964+00:00
-- url     : https://prove2.me/theorems/331c6ebb-fdb7-4a3c-b211-e79df92e3ea1
-- title:
--   Distance Geometry: centered Gram symm
-- statement:
--   The basepoint-centered Gram matrix of a symmetric matrix is symmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L129-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L129-L133

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.centeredGram_symm [NeZero n] {D : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ i j, D i j = D j i) (i j : Fin n) :
    centeredGram D i j = centeredGram D j i := by sorry
