-- Prove2me | Theorems.Thm_DeepLearningTheory_mlp_first_layer_mean_zero
-- name    : DeepLearningTheory.mlp_first_layer_mean_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:17:48.355984+00:00
-- url     : https://prove2.me/theorems/9c606f3e-6cf9-4d7a-ae05-d4202a5472d8
-- title:
--   MLP: first-layer mean vanishes (eq. 4.6)
-- statement:
--   For an MLP at initialization (eqs. 4.3–4.4), every input $x$ and every first-layer neuron $i$,
--
--   $$\mathbb{E}\big[z^{(1)}_i(x)\big]=0.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §4.1, p. 74, eq. (4.6) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem mlp_first_layer_mean_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (x : ℕ → ℝ) (i : ℕ) (hi : i < n 1) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) x 1 i ∂P = 0 := by sorry

end DeepLearningTheory
