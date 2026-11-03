-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_ruin_reward_bound_iff_all_nat_truncations
-- name    : AvramDividend.Classical.avram_wave7_11_original_ruin_reward_bound_iff_all_nat_truncations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:14:05.131045+00:00
-- url     : https://prove2.me/theorems/1e3108c3-0459-47a0-a3ea-35acfb831e9b
-- title:
--   Original full finite-horizon value bound equivalent to uniform natural ruin-clock bounds
-- statement:
--   For the exact original spectrally negative Lévy process X, admissible filtration and source dividend measure, an upper bound b on the full finite-real-horizon expected Stieltjes payout is equivalent to the same uniform b upper bound on every natural ruin-clock truncation. The original right atoms and real endpoint T remain in both sides.
-- source:
--   Direct iff consequence of Proved W7-11 original expected iSup identity 8013d805, providing a reusable deterministic bridge to W7-08 positive-start uniform estimates.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_ruin_reward_bound_iff_all_nat_truncations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (b : ℝ≥0∞) :
    ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b) ↔
    (∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ b) := by sorry
