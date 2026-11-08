-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian19_original_initial_step_reserve_nonneg_positive_capital
-- name    : AvramDividend.Classical.avram_gaussian19_original_initial_step_reserve_nonneg_positive_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:44:25.098503+00:00
-- url     : https://prove2.me/theorems/ecf56090-d6d3-496a-af43-8d1a5c805297
-- title:
--   Initial-step original reserve is locally nonnegative for nonnegative initial capital
-- statement:
--   A sound correction to the original initial-step local-reserve theorem f6cbd410. For the actual original Levy path and initial-only dividend, strict affordability and right-continuity imply a positive interval with nonnegative controlled reserve, provided the initial capital itself is nonnegative. The extra hypothesis is needed because the dividend at time zero is zero.
-- source:
--   Original open f6cbd410 and accepted original dividend-start admissibility be720d99; pinned Mathlib neighbourhood basis NNReal.nhds_zero_basis. This corrected theorem supports initial-dividend and ruin-time arguments without altering the source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussian19_original_initial_step_reserve_nonneg_positive_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      rightLimit (fun s η => if s = 0 then 0 else K η) t ω = K ω)
    (hzero : X.X 0 ω = 0)
    (hcont : ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0)
    (hgap : K ω < x) (hx : 0 ≤ x) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
      0 ≤ riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω := by sorry
