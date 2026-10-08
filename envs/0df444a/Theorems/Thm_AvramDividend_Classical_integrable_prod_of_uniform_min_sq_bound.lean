-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_prod_of_uniform_min_sq_bound
-- name    : AvramDividend.Classical.integrable_prod_of_uniform_min_sq_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:42:28.340139+00:00
-- url     : https://prove2.me/theorems/9e889cb0-e38e-4a13-ad51-796598859930
-- title:
--   Uniform Lévy quadratic domination implies integrability on a product measure
-- statement:
--   For a finite measure μ on the first real coordinate and a measure ν on the second real coordinate with integrable min(1,y²), every jointly almost-everywhere strongly measurable real function f(x,y) satisfying |f(x,y)|≤C min(1,y²) for one fixed C≥0 is integrable under the product measure μ⊗ν. The proof uses integrable constant times integrable moment on the product, followed by domination. This is the abstract final step in turning compact-uniform Lévy compensated-increment estimates into the integrability required for Fubini.
-- source:
--   Elementary dominated integrability and product-measure lemma for the compact-localised Lévy generator argument in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem integrable_prod_of_uniform_min_sq_bound
    (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (hmoment : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (f : ℝ × ℝ → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p : ℝ × ℝ, ‖f p‖ ≤ C * min 1 (p.2 ^ 2)) :
    Integrable f (μ.prod ν) := by sorry

end AvramDividend.Classical
