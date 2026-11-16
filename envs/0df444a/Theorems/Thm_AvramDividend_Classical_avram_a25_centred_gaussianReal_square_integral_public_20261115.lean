-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_centred_gaussianReal_square_integral_public_20261115
-- name    : AvramDividend.Classical.avram_a25_centred_gaussianReal_square_integral_public_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:58:26.060957+00:00
-- url     : https://prove2.me/theorems/dacb78ea-4f02-42e0-beff-32f1e2629a03
-- title:
--   Centred real Gaussian has integrable square and exact variance as its second moment
-- statement:
--   For every nonnegative Gaussian variance v, the square of the identity is integrable under gaussianReal(0,v) and its integral equals v. Follows directly from Mathlib memLp_id_gaussianReal and memLp_two_iff_integrable_sq for integrability, and variance_id_gaussianReal with variance_eq_integral and mean zero for the value. This is reusable for the original Lévy Gaussian residual square-moment target. Preamble opens only declared Mathlib namespaces, avoiding an unbound custom namespace.
-- source:
--   Pinned Mathlib ProbabilityTheory.variance_id_gaussianReal, integral_id_gaussianReal, MeasureTheory.memLp_two_iff_integrable_sq.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_centred_gaussianReal_square_integral_public_20261115 (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) ∧
      (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by sorry
