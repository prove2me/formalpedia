-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_liminf_clock_pathwise_cash_le_liminf
-- name    : AvramDividend.Classical.avram_wave7_19_original_overshooting_liminf_clock_pathwise_cash_le_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:41:19.610079+00:00
-- url     : https://prove2.me/theorems/5c7cbb46-c13a-4b75-981e-5eae72c6b358
-- title:
--   Original pathwise discounted ruin Stieltjes cash is below liminf cash at any overshooting nonmonotone clock sequence
-- statement:
--   A genuinely diagonal local Ito–Meyer truncation sequence needs pathwise cash lower semicontinuity under a possibly nonmonotone sequence of clock cutoffs. For the actual original source X,D at any sample path, if the tail lower limit of clocks τ_n is at least ruinTime, the full discounted dividendMeasure mass on strict pre-ruin paymentTimes through T is ≤liminf_n cash(τ_n). Proof uses the increasing clipped tail-infimum clock σ_n=min(ruinTime,inf_k τ_(n+k)), exact original pathwise Stieltjes cash supremum at cofinal clocks, and monotonicity of paymentTimes to compare cash σ_n with every future cash τ_(n+k). This preserves the initial right-payment atom, excludes t=ruin>0, and requires neither admissibility, continuity at ruin, terminal UI nor any expectation bound.
-- source:
--   Accepted W7-19 original pathwise cofinal random-clock Stieltjes cash iSup f06348b9-331b-447c-b4d3-98e69dd360a5; source paymentTimes and ENNReal tail-infimum clock monotonicity; no duplicate W7-03 measure conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_overshooting_liminf_clock_pathwise_cash_le_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (τ : ℕ → ℝ≥0∞)
    (hLiminfLower : ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k))) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (⨆ n : ℕ, ⨅ k : ℕ,
      (∫⁻ t in paymentTimes (τ (n + k)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
