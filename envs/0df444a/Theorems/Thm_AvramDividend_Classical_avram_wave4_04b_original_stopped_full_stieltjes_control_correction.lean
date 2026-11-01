-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_stopped_full_stieltjes_control_correction
-- name    : AvramDividend.Classical.avram_wave4_04b_original_stopped_full_stieltjes_control_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:07:31.571225+00:00
-- url     : https://prove2.me/theorems/85c80889-6ed0-4ecf-a6f2-db7494e5550d
-- title:
--   Direct original finite-horizon stopped Stieltjes cash reward controlled by complete chronological dividends
-- statement:
--   For the genuine spectrally negative Lévy surplus and adapted dividend strategy, the original discounted Stieltjes dividend integral over paymentTimes τ intersected with times at most T is bounded by the full sum of chronological right-payment test-function secants and an integral of the HJB gradient against the complete atomless dividend Stieltjes remainder, including singular-continuous mass. Local gradient and chronological jump premises are required only at paid times with strict interior reserve. This is the direct source-to-Chat04 finite-variation control interface, not the still-missing stochastic Ito–Meyer identity.
-- source:
--   Two already canonically Proved 04-B imports: exact stopped-window complete-control correction a795b6a3, and original reward = finite closed-horizon restriction 122d4c4b. No circular or speculative stochastic premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_payment_complete_control_correction_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_original_stopped_full_stieltjes_control_correction
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
      (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
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
