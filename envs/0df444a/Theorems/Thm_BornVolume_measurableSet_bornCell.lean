-- Prove2me | Theorems.Thm_BornVolume_measurableSet_bornCell
-- name    : BornVolume.measurableSet_bornCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:27.670286+00:00
-- url     : https://prove2.me/theorems/3c5a1ae8-1954-4eda-a982-bad61d965e7a
-- title:
--   Born Volume: measurable Set born Cell
-- statement:
--   Each Born cell is measurable.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L127-L135
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornFrequency.lean#L127-L135

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

theorem BornVolume.measurableSet_bornCell (ψ : EuclideanSpace ℂ (Fin (M + 1))) (i : Fin (M + 1)) :
    MeasurableSet (bornCell ψ i) := by sorry
