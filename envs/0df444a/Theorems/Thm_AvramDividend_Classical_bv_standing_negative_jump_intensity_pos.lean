-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_standing_negative_jump_intensity_pos
-- name    : AvramDividend.Classical.bv_standing_negative_jump_intensity_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:29:12.288614+00:00
-- url     : https://prove2.me/theorems/241e676d-95e7-4bd2-9ccf-49605b30ac7f
-- title:
--   Nonmonotone bounded-variation Lévy processes have strictly positive negative-jump intensity
-- statement:
--   The Proved bv_standing_drift_pos establishes ν≠0. Spectral negativity gives ν(Ici 0)=0. Since ℝ splits into negative and nonnegative half-lines, ν(Iio 0)>0. Used for the positive first-jump hazard in the finite-activity zero-barrier branch.
-- source:
--   bv_standing_drift_pos proved theorem 0432f641-b22a-4ba0-b92e-6972ea7a1908, X.ν_Ici support.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_standing_negative_jump_intensity_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    0 < X.ν (Iio (0 : ℝ)) := by sorry
