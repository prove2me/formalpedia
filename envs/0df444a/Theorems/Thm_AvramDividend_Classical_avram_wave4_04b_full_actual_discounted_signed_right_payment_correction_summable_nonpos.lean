-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_actual_discounted_signed_right_payment_correction_summable_nonpos
-- name    : AvramDividend.Classical.avram_wave4_04b_full_actual_discounted_signed_right_payment_correction_summable_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:23:06.021806+00:00
-- url     : https://prove2.me/theorems/47f65293-d5c7-41ca-9e54-6a33ea2f1eaf
-- title:
--   Absolute convergence and nonpositivity of complete actual right-dividend correction under localized secant and hjump bounds
-- statement:
--   Take precisely every positive chronological right-payment atom of the original dividend measure on [0,T], including at t=0, not a chosen finite subset. Its actual payment sizes are summable by the prior source theorem. Under an explicit uniform finite secant-growth bound and the genuine per-payment HJB hjump inequality for this window, the entire discounted signed nonlinear right-payment correction converges absolutely and is nonpositive. The secant-growth hypothesis is a separate localized regularity condition, not deduced from an interior derivative lower bound at boundary contact.
-- source:
--   04-B complete actual right-atom signed correction with true support and explicit localization regularity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_full_actual_discounted_signed_right_payment_correction_summable_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (A : Set ℝ)
    (hA : A = {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
      0 < rightLimit D s.toNNReal ω - D s.toNNReal ω})
    (L : ℝ) (hL : 0 ≤ L)
    (hjump : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hSecant : ∀ s : A, |((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))| ≤
      L * (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) :
    Summable (fun s : A =>
      Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ∧
    (∑' s : A,
      Real.exp (-(q * (s : ℝ))) * ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) + w (riskProcess X x D ((s : ℝ).toNNReal) ω - (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) - w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ≤ 0 := by
  sorry
