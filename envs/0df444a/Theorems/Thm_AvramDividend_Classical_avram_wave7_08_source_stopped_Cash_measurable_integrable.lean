-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_Cash_measurable_integrable
-- name    : AvramDividend.Classical.avram_wave7_08_source_stopped_Cash_measurable_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:40:18.173807+00:00
-- url     : https://prove2.me/theorems/2be807ce-81b9-46f4-aed4-053675f54c2c
-- title:
--   Original source named stopped Cash is automatically L1 and a.e. strongly measurable
-- statement:
--   For the genuine original source admissible dividend D and any bounded measurable random clock τ, the named real Cash observable equal to the original full ruin-time stopped discounted Stieltjes lintegral.toReal is automatically integrable and a.e. strongly measurable under P. This exactly discharges the hCashMeas premise of the Proved one-sided source HJB budget, with no source Ito assumption.
-- source:
--   Direct application of Proved original W6-08 random-clock Cash integrability theorem 3deca135, which consumes W7-03 Stieltjes measurability and payoff envelope. It preserves all canonical Ω/P/X/D/ruinTime/dividendMeasure data.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_stopped_Cash_measurable_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτBound : ∀ ω, τ ω ≤ T)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    Integrable Cash P ∧ AEStronglyMeasurable Cash P := by sorry
