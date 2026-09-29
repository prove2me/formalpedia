-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_four_point_first_layer
-- name    : DeepLearningTheory.linearNet_four_point_first_layer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:32:26.26861+00:00
-- url     : https://prove2.me/theorems/49dd3bd4-4fba-475a-b7ee-eeb930cfb3d3
-- title:
--   Deep linear network: first-layer four-point correlator (eq. 3.18)
-- statement:
--   For a zero-bias deep linear network at initialization, a single input $x$ and first-layer neurons $i_1,\dots,i_4$,
--
--   $$\mathbb{E}\big[z^{(1)}_{i_1}z^{(1)}_{i_2}z^{(1)}_{i_3}z^{(1)}_{i_4}\big]=C_W^2\,(\delta_{i_1i_2}\delta_{i_3i_4}+\delta_{i_1i_3}\delta_{i_2i_4}+\delta_{i_1i_4}\delta_{i_2i_3})\,\big(G^{(0)}_2\big)^2,\qquad G^{(0)}_2=\frac1{n_0}\sum_{j=1}^{n_0}x_j^2 .$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.3, p. 60, eqs. (3.18)–(3.19) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_four_point_first_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (i₁ i₂ i₃ i₄ : ℕ)
    (hi₁ : i₁ < n 1) (hi₂ : i₂ < n 1) (hi₃ : i₃ < n 1) (hi₄ : i₄ < n 1) :
    ∫ ω, linearPreact n (W ω) x 1 i₁ * linearPreact n (W ω) x 1 i₂ *
        linearPreact n (W ω) x 1 i₃ * linearPreact n (W ω) x 1 i₄ ∂P
      = (CW : ℝ) ^ 2 * wickDelta4 i₁ i₂ i₃ i₄ * inputKernel (n 0) x x ^ 2 := by sorry

end DeepLearningTheory
