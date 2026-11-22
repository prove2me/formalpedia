-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_succ_succ
-- name    : DistanceGeometry.cayleyMenger_succ_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:05.16127+00:00
-- url     : https://prove2.me/theorems/e6a1ef16-257e-44b6-8d5d-914c5ba86045
-- title:
--   Distance Geometry: cayley Menger succ succ
-- statement:
--   The lower-right block of the Cayley–Menger matrix is `D`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L89-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L89-L90

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

theorem DistanceGeometry.cayleyMenger_succ_succ (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) : cayleyMenger D i.succ j.succ = D i j := by sorry

attribute [defeq] DistanceGeometry.cayleyMenger_succ_succ
