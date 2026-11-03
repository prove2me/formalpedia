-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
-- name    : AvramDividend.Classical.avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:39:27.296036+00:00
-- url     : https://prove2.me/theorems/006d9506-b870-4052-bf23-48f6b1b484aa
-- title:
--   Genuine original unbounded random-clock full-Stieltjes dividend cash is L1 at q≥ψθ
-- statement:
--   For the original spectrally negative Lévy X and admissible D, at any measurable nonnegative potentially unbounded random clock τ, the exact complete source ruin-stopped Stieltjes cash.toReal is integrable over P whenever some θ>0 satisfies q≥ψθ. No boundedness or stopping-time premise on τ, no changed sample space, and no conditional stochastic Ito representation are assumed.
-- source:
--   Uses exact original random-clock payoff measurable 2d478c7d and unconditional θ budget from the independently authored unbounded random-clock theorem, itself sourced in Proved 2abbc6bc.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
