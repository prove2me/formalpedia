-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_zero_reserve_active_right_atom_vanishes
-- name    : AvramDividend.Classical.avram_p4_d_dividend_zero_reserve_active_right_atom_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:09:54.493162+00:00
-- url     : https://prove2.me/theorems/2a0a1444-173a-48b7-b425-a2a485fb37f9
-- title:
--   Admissibility makes the original right-payment Stieltjes atom vanish at an active zero-reserve state
-- statement:
--   For the genuine original admissible dividend control, at an active time zero or strictly before ruin, if the post-source-jump pre-dividend reserve U_t is exactly zero, monotonicity gives ΔD_t≥0 and admissibility gives ΔD_t≤U_t=0. Hence the actual original dividendMeasure singleton mass at t is zero. This is a source-derived lower-boundary right-atom result, including time zero and simultaneous Lévy jumps, without assuming derivative regularity at zero.
-- source:
--   Original IsAdmissibleLe/IsAdmissible definitions UUID 561c1e83; proved dividendStrategy_le_rightLimit UUID 953f0e91 and dividendMeasure_singleton_eq_rightLimit_sub UUID 4f229f9a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_zero_reserve_active_right_atom_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hzero : riskProcess X x D t ω = 0) :
    dividendMeasure D ω {(t : ℝ)} = 0 := by sorry
