-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_zero_succ
-- name    : DistanceGeometry.cayleyMenger_zero_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:00.352036+00:00
-- url     : https://prove2.me/theorems/cfc0edaf-5ec3-4026-88bb-3348d6a5b03f
-- title:
--   Distance Geometry: cayley Menger zero succ
-- statement:
--   Off the corner, the first row of the Cayley–Menger matrix is all `1`s.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L81-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L81-L82

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem DistanceGeometry.cayleyMenger_zero_succ (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (j : Fin (n + 1)) : cayleyMenger D 0 j.succ = 1 := by sorry

attribute [defeq] DistanceGeometry.cayleyMenger_zero_succ
