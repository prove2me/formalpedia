-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy
-- name    : AvramDividend.Classical.stopped_discounted_unit_cash_measurable_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:30:37.983237+00:00
-- url     : https://prove2.me/theorems/31ab5134-ad4b-4aea-8dba-f077058ad814
-- title:
--   Measurable exact stopped discounted dividend cash on each half-open unit interval
-- statement:
--   For an admissible left-continuous adapted dividend strategy of a spectrally negative Lévy process, the exact discounted Stieltjes cash on the stopped finite-horizon half-open unit interval [k,k+1) is measurable as an ENNReal-valued function of the sample path. Intersect the proved jointly measurable random payment-time set with the deterministic closed horizon and the half-open unit interval. Apply the proved measurable_random_indicator_lintegral theorem to the already-Proved s-finite random dividend-measure kernel, then convert indicator integration to the restricted Stieltjes lintegral. This theorem and the proved finite-cash lemma make the real cash .toReal measurable and establish hPrefixAE for the Proved exponential_levy_grid_cash_stieltjes_limit_le_initial, hence both open BV/UV stochastic cores. Expected integrability and stopped generator inequality remain open.

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_discounted_unit_cash_measurable_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) (k : ℕ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
