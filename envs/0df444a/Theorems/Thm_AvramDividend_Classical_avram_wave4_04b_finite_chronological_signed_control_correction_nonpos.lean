-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_chronological_signed_control_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_chronological_signed_control_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:59:53.478634+00:00
-- url     : https://prove2.me/theorems/13738ca9-6f04-4a9c-a729-8277f0254c97
-- title:
--   Signed discounted chronological right-dividend jump corrections are nonpositive on every finite payment set
-- statement:
--   On the genuine controlled spectrally negative Lévy path with any adapted dividend strategy, for every finite set of right-payment times inside a finite horizon and stopped payment window, the exact discounted signed nonlinear Itô–Meyer dividend-jump correction has nonpositive sum under the source chronological hjump condition. This includes t=0 and simultaneous Lévy source jumps and does not assume atomic concentration of the full Stieltjes dividend measure. The result is finite-set sign control, not an unproved infinite stochastic jump formula.
-- source:
--   Exact source payment jump convention rightLimit D−D, riskProcess post-X/pre-D, elementary Finset.sum_nonpos and positivity of exponential; complements canonically Proved chronological jump separation 14ce41c4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_finite_chronological_signed_control_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (F : Finset ℝ≥0)
    (hFT : ∀ t ∈ F, t ≤ T)
    (hFP : ∀ t ∈ F, (t : ℝ) ∈ paymentTimes τ)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω))) ≤ 0 := by sorry
