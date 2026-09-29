-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_four_point_recursion
-- name    : DeepLearningTheory.linearNet_four_point_recursion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:37:57.033836+00:00
-- url     : https://prove2.me/theorems/62c07ebb-1143-43da-998f-4768ba4a8536
-- title:
--   Deep linear network: four-point recursion (eq. 3.20)
-- statement:
--   For a zero-bias deep linear network at initialization and a single input $x$, for every layer $\ell\ge0$ and neurons $i_1,\dots,i_4$ of layer $\ell+1$,
--
--   $$\mathbb{E}\big[z^{(\ell+1)}_{i_1}z^{(\ell+1)}_{i_2}z^{(\ell+1)}_{i_3}z^{(\ell+1)}_{i_4}\big]=C_W^2\,(\delta_{i_1i_2}\delta_{i_3i_4}+\delta_{i_1i_3}\delta_{i_2i_4}+\delta_{i_1i_4}\delta_{i_2i_3})\,\frac1{n_\ell^2}\sum_{j,k=1}^{n_\ell}\mathbb{E}\big[z^{(\ell)}_jz^{(\ell)}_jz^{(\ell)}_kz^{(\ell)}_k\big].$$
--
--   **Formalization Note** The identity is stated for all $\ell\ge0$; for $\ell=0$ the right side involves the deterministic input and reduces to eq. (3.18).
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.3, pp. 60–61, eq. (3.20) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_four_point_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ i₁ i₂ i₃ i₄ : ℕ)
    (hi₁ : i₁ < n (ℓ + 1)) (hi₂ : i₂ < n (ℓ + 1)) (hi₃ : i₃ < n (ℓ + 1))
    (hi₄ : i₄ < n (ℓ + 1)) :
    ∫ ω, linearPreact n (W ω) x (ℓ + 1) i₁ * linearPreact n (W ω) x (ℓ + 1) i₂ *
        linearPreact n (W ω) x (ℓ + 1) i₃ * linearPreact n (W ω) x (ℓ + 1) i₄ ∂P
      = (CW : ℝ) ^ 2 * wickDelta4 i₁ i₂ i₃ i₄ * (1 / (n ℓ : ℝ) ^ 2) *
          ∑ j ∈ Finset.range (n ℓ), ∑ k ∈ Finset.range (n ℓ),
            ∫ ω, linearPreact n (W ω) x ℓ j * linearPreact n (W ω) x ℓ j *
              linearPreact n (W ω) x ℓ k * linearPreact n (W ω) x ℓ k ∂P := by sorry

end DeepLearningTheory
