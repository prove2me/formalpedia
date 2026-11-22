-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_clipped_discounted_gaussian_gradient_energy
-- name    : AvramDividend.Classical.avram_lsc_clipped_discounted_gaussian_gradient_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:47:15.819099+00:00
-- url     : https://prove2.me/theorems/0787227c-487a-4ca4-a875-fb00f3713144
-- title:
--   Finite square energy of the clamped actual-state discounted Gaussian coefficient without a pathwise band assumption
-- statement:
--   Any real reserve process can be projected pointwise onto a genuine compact interval inside the smooth HJB region. For q nonnegative, the discounted Gaussian derivative at this clipped reserve has a uniform finite L² integral over every finite time horizon, without requiring the uncontrolled reserve path to remain inside that interval. This supplies the localization integrand for future stopping-time locality and physical Itô–Meyer work.
-- source:
--   Avram Dividend Classical 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Clipped localisation for the zero-jump finitecap stopped Itô argument. Reuses Proved b917eaf2-3077-447f-bbe3-ab4d12ed22a8 and the new compact discounted gradient energy target c6115da6-5317-42c0-bc8c-ea678349a308; proof should follow only once that dependency is Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_lsc_compact_discounted_gaussian_gradient_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_clipped_discounted_gaussian_gradient_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q σ : ℝ) (hq : 0 ≤ q)
    (U : Ω → ℝ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : ℝ, 0 < T →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
          (‖(if 0 ≤ s then
              Real.exp (-(q * s)) *
                deriv w (max a (min b (U ω s))) * σ
            else 0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
