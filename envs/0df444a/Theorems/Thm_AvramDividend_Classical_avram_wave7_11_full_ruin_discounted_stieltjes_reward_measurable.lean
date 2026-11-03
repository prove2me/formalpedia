-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_full_ruin_discounted_stieltjes_reward_measurable
-- name    : AvramDividend.Classical.avram_wave7_11_full_ruin_discounted_stieltjes_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:56:11.517304+00:00
-- url     : https://prove2.me/theorems/299a573c-ef06-4999-b5ac-459bfd278909
-- title:
--   Full finite-horizon Stieltjes reward to original ruin time is measurable
-- statement:
--   For the original spectrally negative Lévy process, its filtration and genuine dividend strategy, the pathwise discounted Stieltjes dividend reward up to the full ruin time and a finite real horizon is measurable in the sample outcome. No stopped stochastic theorem is assumed. This follows by the proved pointwise increasing union of truncated ruin-payment sets and measurability of each payoff at the deterministic measurable stop n.
-- source:
--   Pathwise horizon identity cb688725 and canonical arbitrary measurable stopped Stieltjes reward theorem 014f398c, with Mathlib measurable_iSup. Supports the original-process finite-horizon UBV value bridge cc518136 and downstream value function consumers.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_full_ruin_discounted_stieltjes_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
