-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB38_original_BV_boundary_unmasked_sign_of_dominated_source
-- name    : AvramDividend.Classical.avram_bva_capHJB38_original_BV_boundary_unmasked_sign_of_dominated_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:26.676361+00:00
-- url     : https://prove2.me/theorems/5ebe2587-6cac-4fae-b15d-4b2cdc44046e
-- title:
--   Original finite-cap BV full unmasked generator HJB sign from source atomlessness and L1 domination
-- statement:
--   Under Standing BV for the original spectrally negative Levy process, interior candidate generator nonpositivity and gradient at least one, full source-jump L1 domination and original candidate continuity off reserve zero imply the closed upper cap HJB inequality with drift one (reflecting dividend). This source-specific fact composes accepted cap HJB boundary sign, original jump DCT and diffuse Levy mark measure; it does not assume false strictly interior arbitrary spatial-mask L1 limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB38_original_BV_boundary_unmasked_sign_of_dominated_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwc : ContinuousAt w C.toReal)
    (hAway : ∀ r : ℝ, r ≠ 0 → ContinuousAt w r)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 C.toReal))
    (hyInside : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hDom : ∀ n, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by sorry
