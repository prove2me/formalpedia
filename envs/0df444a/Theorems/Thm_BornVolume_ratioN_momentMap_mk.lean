-- Prove2me | Theorems.Thm_BornVolume_ratioN_momentMap_mk
-- name    : BornVolume.ratioN_momentMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:22.52745+00:00
-- url     : https://prove2.me/theorems/cbc76a56-14e9-483e-9bfa-a0d0f70f0c67
-- title:
--   Born Volume: ratio N moment Map mk
-- statement:
--   The free moment coordinates of the ray of a unit vector are its squared coordinate moduli.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L51-L55
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L51-L55

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.ratioN_momentMap_mk (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)
      = fun k => ‖ψ (Fin.castSucc k)‖ ^ 2 := by sorry
