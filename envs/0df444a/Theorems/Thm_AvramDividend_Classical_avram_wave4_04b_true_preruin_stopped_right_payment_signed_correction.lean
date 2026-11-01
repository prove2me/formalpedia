-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
-- name    : AvramDividend.Classical.avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:24:01.266996+00:00
-- url     : https://prove2.me/theorems/1966d54f-340b-4d6b-836d-939a2308ec62
-- title:
--   Complete true pre-ruin chronological right-payment correction is summable and nonpositive under the original restricted hjump
-- statement:
--   On the complete actual finite-horizon right-payment support restricted to paymentTimes(ruinTime X x D ω), including the time-zero right atom and every strictly pre-ruin payment, the entire discounted nonlinear correction is absolutely summable and nonpositive. The exact jump hypothesis is only the source-corrected UBV one (t=0 or t<ruinTime); no jump inequality at a ruin terminal time or at any post-ruin time is assumed. A separate finite uniform secant-growth bound on the stopped positive atoms supplies absolute convergence, and full actual right-atom summability supplies total finite variation. Source X, D, filtration and chronological post-source-payment reserve are unchanged; singular-continuous and absolutely continuous dividend components are not discarded.
-- source:
--   Avram Wave4 04-B localised complete stopped right-control correction with the exact Chat04 pre-ruin hjump scope; source-compatible deterministic prerequisite for full Itô–Meyer

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_true_preruin_stopped_right_payment_signed_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
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
      L * (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) :
    Summable (fun s : A =>
      Real.exp (-(q * (s : ℝ))) *
        ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
          w (riskProcess X x D ((s : ℝ).toNNReal) ω -
            (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
          w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ∧
    (∑' s : A, Real.exp (-(q * (s : ℝ))) *
      ((rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((s : ℝ).toNNReal) ω -
          (rightLimit D ((s : ℝ).toNNReal) ω - D ((s : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((s : ℝ).toNNReal) ω))) ≤ 0 := by
  sorry
