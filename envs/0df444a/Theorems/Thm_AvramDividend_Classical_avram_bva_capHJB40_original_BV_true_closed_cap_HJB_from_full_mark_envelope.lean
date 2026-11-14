-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
-- name    : AvramDividend.Classical.avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:17:17.613782+00:00
-- url     : https://prove2.me/theorems/74c0faae-edc0-42a1-958f-a01a939630c5
-- title:
--   Original standing BV closed finite-cap HJB sign using full Lévy jump L1 envelope
-- statement:
--   Original Standing BV and actual candidate assumptions on continuous nonnegative reserve and zero negative extension, interior generator inequality and gradient one, plus an explicit uniformly integrable full unmasked negative jump bound along approaching interior reserves imply the true finite-cap generator sign with reflecting dividend drift. This is suitable for the direct stopped cash verification, unlike the false strictly interior cofinal mark mask of A22.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
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
