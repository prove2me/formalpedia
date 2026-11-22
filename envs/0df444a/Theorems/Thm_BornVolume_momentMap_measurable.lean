-- Prove2me | Theorems.Thm_BornVolume_momentMap_measurable
-- name    : BornVolume.momentMap_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:06.509786+00:00
-- url     : https://prove2.me/theorems/e0007490-edb6-4c23-af50-eb46397a2682
-- title:
--   Born Volume: moment Map measurable
-- statement:
--   **`momentMap · i` is measurable.** `momentMap` is defined via the
--   representative `rep`, but it is scale-invariant, so it descends from the
--   measurable function `v ↦ ‖vᵢ‖²/‖v‖²` on the nonzero subtype, by
--   `Projectivization.measurable_iff_measurable_comp_mk'`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMeasurable.lean#L31-L47
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMeasurable.lean#L31-L47

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_BornVolumeLean_Volume_MomentMeasurable
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}

theorem BornVolume.momentMap_measurable (i : Fin N) :
    Measurable (fun p : CPN N => momentMap p i) := by sorry
