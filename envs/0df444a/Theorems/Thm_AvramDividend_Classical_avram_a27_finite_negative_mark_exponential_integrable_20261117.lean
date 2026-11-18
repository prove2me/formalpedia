-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_finite_negative_mark_exponential_integrable_20261117
-- name    : AvramDividend.Classical.avram_a27_finite_negative_mark_exponential_integrable_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:25:51.662378+00:00
-- url     : https://prove2.me/theorems/fbfe360f-791d-4684-8ccf-266e78e059ee
-- title:
--   Finite negative Lévy mark measure admits every nonnegative-tilt exponential moment
-- statement:
--   For a finite measure on the negative real marks, the nonnegative-tilt exponential e^(theta*y) is integrable. This provides a finite one-mark moment for the original physical negative-jump Poisson law without auxiliary randomisation.
-- source:
--   Pinned accepted proof of A75 source negative mark exponential integrability and bounded finite-measure dominated integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite negative mark measure integrates every nonnegative-tilt exponential. -/

theorem AvramDividend.Classical.avram_a27_finite_negative_mark_exponential_integrable_20261117 (ν : Measure ℝ)
    (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y))
      (Iio (0 : ℝ)) ν := by sorry
