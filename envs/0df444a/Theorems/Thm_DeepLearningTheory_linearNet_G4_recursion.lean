-- Prove2me | Theorems.Thm_DeepLearningTheory_linearNet_G4_recursion
-- name    : DeepLearningTheory.linearNet_G4_recursion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:41:23.501244+00:00
-- url     : https://prove2.me/theorems/be429d52-5699-4740-9b36-a4ee65d5937a
-- title:
--   Deep linear network: $G_4^{(\ell+1)}=C_W^2(1+2/n_\ell)G_4^{(\ell)}$ (eqs. 3.21–3.24)
-- statement:
--   For a zero-bias deep linear network with positive widths at initialization and a single input $x$, let $\ell\ge1$ and suppose the layer-$\ell$ four-point correlator has the Wick tensor structure with coefficient $G_4^{(\ell)}$:
--
--   $$\mathbb{E}\big[z^{(\ell)}_{i_1}z^{(\ell)}_{i_2}z^{(\ell)}_{i_3}z^{(\ell)}_{i_4}\big]=(\delta_{i_1i_2}\delta_{i_3i_4}+\delta_{i_1i_3}\delta_{i_2i_4}+\delta_{i_1i_4}\delta_{i_2i_3})\,G_4^{(\ell)}\quad\text{for all }i_1,\dots,i_4 .$$
--
--   Then the layer-$(\ell+1)$ correlator has the same structure with
--
--   $$G_4^{(\ell+1)}=C_W^2\Big(1+\frac{2}{n_\ell}\Big)G_4^{(\ell)}.$$
-- source:
--   Daniel A. Roberts and Sho Yaida (with Boris Hanin), *The Principles of Deep Learning Theory*, arXiv:2106.10165v2, https://arxiv.org/abs/2106.10165, §3.3, p. 61, eqs. (3.21)–(3.24) (page numbers are the book's printed page numbers)

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DeepLearningTheory

theorem linearNet_G4_recursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (hn : ∀ ℓ, 0 < n ℓ) (CW : ℝ≥0)
    (W : Ω → ℕ → ℕ → ℕ → ℝ) (hW : IsLinearNetInit P n CW W) (x : ℕ → ℝ) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (G4 : ℝ)
    (hG4 : ∀ i₁ i₂ i₃ i₄, i₁ < n ℓ → i₂ < n ℓ → i₃ < n ℓ → i₄ < n ℓ →
      ∫ ω, linearPreact n (W ω) x ℓ i₁ * linearPreact n (W ω) x ℓ i₂ *
        linearPreact n (W ω) x ℓ i₃ * linearPreact n (W ω) x ℓ i₄ ∂P
        = wickDelta4 i₁ i₂ i₃ i₄ * G4)
    (i₁ i₂ i₃ i₄ : ℕ) (hi₁ : i₁ < n (ℓ + 1)) (hi₂ : i₂ < n (ℓ + 1))
    (hi₃ : i₃ < n (ℓ + 1)) (hi₄ : i₄ < n (ℓ + 1)) :
    ∫ ω, linearPreact n (W ω) x (ℓ + 1) i₁ * linearPreact n (W ω) x (ℓ + 1) i₂ *
        linearPreact n (W ω) x (ℓ + 1) i₃ * linearPreact n (W ω) x (ℓ + 1) i₄ ∂P
      = wickDelta4 i₁ i₂ i₃ i₄ * ((CW : ℝ) ^ 2 * (1 + 2 / (n ℓ : ℝ)) * G4) := by sorry

end DeepLearningTheory
