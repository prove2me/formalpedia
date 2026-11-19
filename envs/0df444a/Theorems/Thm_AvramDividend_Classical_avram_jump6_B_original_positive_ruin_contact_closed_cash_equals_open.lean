-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_contact_closed_cash_equals_open
-- name    : AvramDividend.Classical.avram_jump6_B_original_positive_ruin_contact_closed_cash_equals_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:00:44.10175+00:00
-- url     : https://prove2.me/theorems/0a89e654-512c-4a1a-b285-ecebcf2b62f4
-- title:
--   True original positive ruin-contact stopped closed-Iic dividend cash equals open-right ruin cash
-- statement:
--   For the original spectrally negative Levy X and actual admissible dividend D, any original random stop sigma(k) beneath exact ruin-clipped tau, positive and equal to ruinTime, the discounted paymentTimes∩Iic stopped cash equals the original dividendMeasure discounted Ico(0,sigma) cash. This exactly removes the ruin-contact endpoint from the original inclusive cash and supports the original positive ruin-contact signed stochastic payment residual branch. No finite activity or substitute process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_positive_ruin_contact_closed_cash_equals_open
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ η, τ η =
      (min (ruinTime X x D η) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k η, σ k η ≤ τ η)
    (k : ℕ) (ω : Ω)
    (hPos : σ k ω ≠ 0)
    (hContact : (σ k ω : ℝ≥0∞) = ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ s in Ico (0 : ℝ) (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
