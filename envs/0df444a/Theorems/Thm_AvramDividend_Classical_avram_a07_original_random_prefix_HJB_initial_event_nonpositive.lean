-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_random_prefix_HJB_initial_event_nonpositive
-- name    : AvramDividend.Classical.avram_a07_original_random_prefix_HJB_initial_event_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:47:31.939727+00:00
-- url     : https://prove2.me/theorems/0cbf5718-ba12-495f-bc0d-91ab0d3f3c55
-- title:
--   Random stopped original HJB grid has nonpositive initial-event integral
-- statement:
--   At a genuinely random prefix of the controlled dividend process grid, the full discounted HJB generator and dividend gradient remainder has nonpositive integral over any initial-filtration event. This is the conditional stochastic clock HJB sign needed in the original Ito-Meyer estimate.
-- source:
--   Initial-event integral of physical random prefix theorem

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_random_prefix_HJB_initial_event_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (k : Ω → ℕ)
    (hregion : ∀ ω i, i < k ω →
      0 < riskProcess X x D (u i) ω ∧
      ENNReal.ofReal (riskProcess X x D (u i) ω) < C)
    (G : Ω → ℝ)
    (hG : ∀ ω, G ω =
      (∑ i ∈ Finset.range (k ω),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) *
            (X.generator w (riskProcess X x D (u i) ω) -
              q * w (riskProcess X x D (u i) ω)) +
          (D (u (i + 1)) ω - D (u i) ω) *
            (1 - deriv w (riskProcess X x D (u i) ω)))))
    (hGI : Integrable G P) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, G ω ∂P) ≤ 0 := by sorry
