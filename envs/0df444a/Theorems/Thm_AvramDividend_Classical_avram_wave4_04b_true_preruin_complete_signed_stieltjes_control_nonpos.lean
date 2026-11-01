-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_true_preruin_complete_signed_stieltjes_control_nonpos
-- name    : AvramDividend.Classical.avram_wave4_04b_true_preruin_complete_signed_stieltjes_control_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:36:18.897743+00:00
-- url     : https://prove2.me/theorems/52211097-300e-400d-a013-ac4cd080016c
-- title:
--   True pre-ruin right-payment correction plus a specified atomless Stieltjes correction is nonpositive
-- statement:
--   The full discounted finite-variation control correction on an actual source-X stopped path is nonpositive, including the complete countable chronological right-payment corrections at true pre-ruin payment times and a specified atomless measure ν that can be instantiated as the independently constructed diffuse Stieltjes dividend component, including singular-continuous variation. The jump condition has precisely the corrected UBV time-zero-or-pre-ruin scope. The derivative bound is used only on the declared interior localisation support. The genuine finite-window secant constant and real diffuse integrability are explicit; no stochastic Itô–Meyer generator balance or martingale integrability is assumed/proved.
-- source:
--   04-B exact-source stopped Stieltjes signed correction; combines two fully Proved source-specific components without touching Chat04 canonical UBV upper bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_true_preruin_complete_signed_stieltjes_control_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ)
    (hA : A = {s : ℝ | s ∈ paymentTimes (ruinTime X x D ω) ∧
      s ≤ (T : ℝ) ∧ 0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (L : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSecant : ∀ s : A,
      |(rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω)| ≤
      L * (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω))
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) ν) :
    (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' s : A, Real.exp (-(q * (s : ℝ))) *
      ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ≤ 0 := by
  sorry
