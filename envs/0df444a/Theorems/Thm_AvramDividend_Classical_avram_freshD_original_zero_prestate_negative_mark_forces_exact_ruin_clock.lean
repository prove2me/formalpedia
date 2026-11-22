-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_zero_prestate_negative_mark_forces_exact_ruin_clock
-- name    : AvramDividend.Classical.avram_freshD_original_zero_prestate_negative_mark_forces_exact_ruin_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T09:00:51.500595+00:00
-- url     : https://prove2.me/theorems/e80f8930-0be3-415b-9e41-e8b6bc781127
-- title:
--   An actual negative Lévy mark from zero predictable reserve at or before ruin occurs exactly at original ruin clock
-- statement:
--   For the genuine original negative Lévy source jump at physical time t, if the exact pre-dividend pre-jump controlled reserve x+X(t-)-D(t) is zero and the negative mark occurs at or before the original ruin clock, then t equals the ruin clock. The actual post-jump riskProcess at t equals the negative mark and is therefore strictly negative, forcing the first negative-reserve hitting infimum no later than t; combine with the supplied t≤ruin bound. This isolates the only zero-prestate negative mark possible before or at ruin as a terminal exceptional marked cell. It retains the exact canonical ruin clock and does not discard terminal jumps or assume w(0)=0.
-- source:
--   Original physical stopped finite-activity marked cash-excess root 242ca5f1: zero-boundary mark exception and original ruinTime infimum definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_zero_prestate_negative_mark_forces_exact_ruin_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hzero : x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω = 0)
    (hz : X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0) :
    (t : ℝ≥0∞) = ruinTime X x D ω := by sorry
