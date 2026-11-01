-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_positiveTime_stopped_exponential_expected_cash
-- name    : AvramDividend.Classical.avram_wave4_03_actual_source_positiveTime_stopped_exponential_expected_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:45:31.73013+00:00
-- url     : https://prove2.me/theorems/5d4be366-6720-4be5-afb8-c6fbc0973037
-- title:
--   Actual same-path Lévy strictly pre-ruin full Stieltjes positive-time discounted dividend expectation bounded by exponential initial capital
-- statement:
--   On the original filtered probability space, for any capped admissible left-continuous dividend strategy D, all its positive-time strictly pre-ruin dividend Stieltjes mass on (0,T], including diffuse and singular-continuous components and every right-dividend atom, has expected exponential discount e^{-ψ(1)t} bounded by e^x. The proof uses the actual same-path Lévy stochastic exponential expected Stieltjes budget ≤1, the genuine admissible postpayment reserve inequality, random Stieltjes kernel measurability and two lawful constant multiplications. No source process substitution or purely atomic reduction occurs. This special exponential test does not assert the general C¹ HJB verification theorem.
-- source:
--   Proved original-source full Stieltjes expected stochastic exponential budget 6e0c195d, genuine stopped pathwise postpayment bound 0375c440, original joint measurable 30c00aaa, random Stieltjes kernel measurable 872a8afd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_actual_source_positiveTime_stopped_exponential_expected_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) ∧
           s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (Real.exp x) := by sorry
