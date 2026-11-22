-- Prove2me | Theorems.Thm_BornVolume_measurable_freeMoment
-- name    : BornVolume.measurable_freeMoment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:07.668635+00:00
-- url     : https://prove2.me/theorems/9a496a73-3233-4612-b2a5-c5116c1d21b0
-- title:
--   Born Volume: measurable free Moment
-- statement:
--   The free-coordinate Born vector `p ↦ (k ↦ momentMap p (Fin.castSucc k))` is measurable.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L122-L124
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L122-L124

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.measurable_freeMoment :
    Measurable (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) := by sorry
