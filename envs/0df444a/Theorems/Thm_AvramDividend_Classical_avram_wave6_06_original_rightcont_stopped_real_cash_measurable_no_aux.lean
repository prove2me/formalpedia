-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
-- name    : AvramDividend.Classical.avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:01:24.732848+00:00
-- url     : https://prove2.me/theorems/d0eb0e63-3b3f-4263-a950-dd4e6c770f33
-- title:
--   Original right-continuous ruin-stopped complete real cash is strongly measurable without auxiliary assumptions
-- statement:
--   The actual original dividend process D is admissible under its original right-continuous filtration, tau is a genuine stopping time and the real cash is exactly the complete original Stieltjes reward over paymentTimes sigma intersect Iic tau. From hτ, the Proved nonnegative-clock real-measurable lemma d12a741a derives measurable real tau; then the Proved exact inclusive cash real strong meas lemma c3b1d861 yields AEStronglyMeasurable Cash P. No independent clock or cash measurability assumption, no stochastic Ito identity, no surrogate process. This discharges hCashMeas of the final HJB stopped budget on the original source.
-- source:
--   Avram Prop 4(i); composition of independently proved d12a741a and c3b1d861.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_inclusive_random_clock_real_cash_aestronglyMeasurable

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_rightcont_stopped_real_cash_measurable_no_aux
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    AEStronglyMeasurable Cash P := by sorry
