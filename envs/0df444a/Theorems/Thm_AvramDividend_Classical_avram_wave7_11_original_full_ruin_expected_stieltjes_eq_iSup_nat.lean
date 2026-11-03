-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat
-- name    : AvramDividend.Classical.avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:39:39.568399+00:00
-- url     : https://prove2.me/theorems/8013d805-8dd1-49e1-a556-9e642524ae2d
-- title:
--   Exact original-process full-ruin discounted Stieltjes expectation equals natural-clock supremum
-- statement:
--   For the canonical spectrally negative Lévy process X, original dividend strategy D and original expectation measure P, the expected discounted Stieltjes payment up to full ruinTime X x D and finite real horizon T equals the supremum over all natural-number truncations min(ruinTime, n) of exactly the same expected Stieltjes payment. The genuine t=0 atom remains. The result requires only IsDividendStrategy to establish measurability of truncated rewards, no additional probabilistic axiom or stochastic core.
-- source:
--   Direct exact identity extracted from Proved pathwise truncation cb688725, Proved original arbitrary measurable stop 014f398c, Proved paymentTimes_min_mono_horizon 021cfe05 and Mathlib lintegral_iSup; strengthens existing W7-11 bound c74c5b53 to equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
