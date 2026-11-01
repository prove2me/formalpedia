-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_payment_complete_control_correction_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_stopped_payment_complete_control_correction_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:53:34.38446+00:00
-- url     : https://prove2.me/theorems/a795b6a3-1eb0-463e-b5fc-73398ac851a7
-- title:
--   Exact stopped Stieltjes cash reward controlled by chronological right atoms and all diffuse dividends
-- statement:
--   For the actual spectrally negative Lévy controlled surplus and adapted dividends, an arbitrary finite horizon, stopping/payment clock and discount rate, the full paymentTimes-restricted Stieltjes reward is dominated by the chronological per-payment jump secants plus the derivative-weighted atomless Stieltjes integral. All right-payment atoms, initial and terminal as allowed by the strict stopping indicator, and all singular-continuous and absolutely continuous variation are present. The interior gradient and chronological hjump assumptions are only needed at actual paid times within [0,T]. No claim about the stochastic generator, martingale or Ito–Meyer equality is made.
-- source:
--   Previously canonically Proved avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction and paymentTimes_measurable with Mathlib lintegral_indicator; source-specific stopped-window specialization.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_stopped_payment_complete_control_correction_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes τ, ENNReal.ofReal (Real.exp (-q * s)) ∂μ) ≤
      (∑' t : A,
        ENNReal.ofReal
          (w (riskProcess X x D (t : ℝ).toNNReal ω) -
            w (riskProcess X x D (t : ℝ).toNNReal ω -
              (rightLimit D (t : ℝ).toNNReal ω -
                D (t : ℝ).toNNReal ω))) *
        (paymentTimes τ).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-q * s)) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by sorry
