-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route6_bv_admissible_physical_full_hjb_sum_nonpos
-- name    : AvramDividend.Classical.avram_route6_bv_admissible_physical_full_hjb_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:23:51.698198+00:00
-- url     : https://prove2.me/theorems/09743d18-79c3-46a8-99ef-fc4c520e57b1
-- title:
--   Admissible original BV dividend strategy physical-grid discounted complete HJB sign
-- statement:
--   Specialises the full finite-grid HJB sign to an actual admissible original dividend strategy, deriving the nonnegative D increments from the genuine IsDividendStrategy monotonicity field. The only remaining cell premise is that selected physical nodes are in the positive interior of the cap; stochastic compensation, contact cells, and horizon atoms remain separate source obligations.
-- source:
--   Original stopped BV physical-grid HJB source with admissibility, intended for c1e2f021 and b39f2dd1 after localization, compensation and terminal/cash accounting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route6_bv_admissible_physical_full_hjb_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (cells : Finset ℕ)
    (hregion : ∀ i ∈ cells,
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    (∑ i ∈ cells,
      Real.exp (-(q * (u i : ℝ))) *
        (((u (i + 1) : ℝ) - (u i : ℝ)) *
          (X.generator w (riskProcess X x D (u i) ω) -
            q * w (riskProcess X x D (u i) ω)) +
        (D (u (i + 1)) ω - D (u i) ω) *
          (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by sorry
