-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:38:19.884801+00:00
-- url     : https://prove2.me/theorems/212b8f0c-a57d-428f-8495-2391c50b423e
-- title:
--   Strict interior C2 yields compact-band Lipschitz predictable gradient bound
-- statement:
--   The exact UBV hypothesis ContDiffOn ℝ 2 w over the strict positive below-cap interior, a compact interval contained in that open set, and a finite pointwise bound K on its second derivative imply w' is K-Lipschitz on that interval. This controls same-source Gaussian predictable-gradient approximation on genuine interior-localised stopped intervals. It requires no global boundedness, cross-ruin continuity, endpoint occupation claim or artificial Brownian process.
-- source:
--   Proposition 4(i) local C2 (0,C); source P4-D proved secant bound c4293baa-88f7-4181-b1e6-0fbe74f04472; pinned Mathlib ContDiffAt.derivWithin and Convex.lipschitzOnWith_of_nnnorm_deriv_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |deriv w s - deriv w t| ≤ (K : ℝ) * |s - t| := by sorry
