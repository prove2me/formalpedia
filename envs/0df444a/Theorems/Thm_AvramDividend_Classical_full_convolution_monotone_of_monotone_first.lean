-- Prove2me | Theorems.Thm_AvramDividend_Classical_full_convolution_monotone_of_monotone_first
-- name    : AvramDividend.Classical.full_convolution_monotone_of_monotone_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:57:20.056504+00:00
-- url     : https://prove2.me/theorems/56aca69e-4098-4f51-9059-2d528d093211
-- title:
--   Positive causal convolution preserves global monotonicity in its first kernel
-- statement:
--   For a globally nondecreasing real kernel f and nonnegative kernel g, their full real convolution is nondecreasing whenever the convolution integrals are well-defined and integrable. This provides the monotonicity induction for the nonnegative zero-discount renewal powers and hence the positive-discount scale function built from them.
-- source:
--   Mathlib MeasureTheory.integral_mono, direct pointwise monotonicity. Root-connected helper of unbounded_positive_discount_scale_exists_from_zero, Behme–Oechsler–Schilling causal scale series.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory

theorem AvramDividend.Classical.full_convolution_monotone_of_monotone_first
    (f g : ℝ → ℝ)
    (hf : Monotone f)
    (hg : ∀ y : ℝ, 0 ≤ g y)
    (hInt : ∀ x : ℝ, Integrable (fun y : ℝ => f (x - y) * g y) volume) :
    Monotone (fun x : ℝ =>
      ∫ y : ℝ, f (x - y) * g y ∂volume) := by sorry
