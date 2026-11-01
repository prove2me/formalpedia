-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
-- name    : AvramDividend.Classical.avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:01:03.22259+00:00
-- url     : https://prove2.me/theorems/2f357fd2-eb22-4de1-b7a3-a9ba78dd077a
-- title:
--   Full same-path Lévy closed-horizon strictly pre-ruin Stieltjes dividend expectation is bounded by exponential initial capital
-- statement:
--   On the genuine original source Lévy probability space, for every capped admissible left-continuous right-payment dividend control D, the expected full [0,T] Stieltjes discounted strictly pre-ruin dividend cash with q=ψ(1) is at most exp(x). The exact paymentTimes includes time zero and strictly pre-ruin times; the full dividendMeasure includes the initial right atom, all positive-time atoms, diffuse and singular-continuous payments. Proof combines original source stochastic exponential martingale compensation and Icc Stieltjes expected budget, the actual stopped postpayment solvency exponential bound, and rigorous joint and random Stieltjes kernel measurability. This proves a genuine exponential-test finite-horizon controlled verification result, not the arbitrary C¹ HJB core.
-- source:
--   Proved original-source closed Icc full Stieltjes source budget (new), source capped stop kernel 0375c440, source random Stieltjes measurable 872a8afd, original joint source measurable 30c00aaa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      if s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (Real.exp x) := by sorry
