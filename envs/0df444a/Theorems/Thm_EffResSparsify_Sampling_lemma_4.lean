-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_lemma_4
-- name    : EffResSparsify.Sampling.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:29.518004+00:00
-- url     : https://prove2.me/theorems/1b8c3451-a624-4062-adcd-0ccc3692c159
-- title:
--   Lemma 4 — $\|\Pi S\Pi-\Pi\Pi\|_2\le\varepsilon$ gives $(1\pm\varepsilon)$ approximation of the Laplacian quadratic form
-- statement:
--   Let $G=(V,E,w)$ be a connected weighted graph with positive edge weights, incidence matrix $B$, diagonal weight matrix $W$, Laplacian $L=B^{\mathsf T}WB$, and $\Pi=W^{1/2}BL^{+}B^{\mathsf T}W^{1/2}$. Let $S=\operatorname{diag}(s)$ be a nonnegative diagonal $E\times E$ matrix and $\varepsilon\in\mathbb R$ with
--   $$\|\Pi S\Pi-\Pi\Pi\|_2\le\varepsilon,$$
--   where $\|\cdot\|_2$ is the spectral (operator $\ell_2$) norm. Put $\tilde L=B^{\mathsf T}W^{1/2}SW^{1/2}B$. Then for every $x\in\mathbb R^V$,
--   $$(1-\varepsilon)\,x^{\mathsf T}Lx\le x^{\mathsf T}\tilde Lx\le(1+\varepsilon)\,x^{\mathsf T}Lx.$$
--
--   This deterministic reduction turns the sparsification problem into a matrix approximation problem for $\Pi$: it remains to show that the random $S$ of Sparsify makes $\Pi S\Pi$ close to $\Pi$ in spectral norm.
--
--   **Formalization Note** The spectral norm is Mathlib's $\ell_2$ operator norm on matrices (`Matrix.Norms.L2Operator`). No sign condition on $\varepsilon$ is imposed, as in the paper; the hypothesis forces $\varepsilon\ge0$.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 7, Lemma 4

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace EffResSparsify.Sampling

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Lemma 4, p. 7: if `S = diag(s)` is a nonnegative diagonal matrix with
`‖Π S Π − Π Π‖₂ ≤ ε` (spectral norm), then for every `x ∈ ℝⁿ`,
`(1 − ε) xᵀ L x ≤ xᵀ L̃ x ≤ (1 + ε) xᵀ L x`, where `L = Bᵀ W B` and
`L̃ = Bᵀ W^{1/2} S W^{1/2} B`. -/
theorem lemma_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (hG : G.IsConnected) (s : E → ℝ) (hs : ∀ e, 0 ≤ s e) (ε : ℝ)
    (hε : ‖G.projPi * Matrix.diagonal s * G.projPi - G.projPi * G.projPi‖ ≤ ε) :
    ∀ x : V → ℝ,
      (1 - ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)) ≤
          x ⬝ᵥ ((G.incidenceᵀ * G.sqrtWeightMatrix * Matrix.diagonal s * G.sqrtWeightMatrix *
            G.incidence) *ᵥ x) ∧
        x ⬝ᵥ ((G.incidenceᵀ * G.sqrtWeightMatrix * Matrix.diagonal s * G.sqrtWeightMatrix *
            G.incidence) *ᵥ x) ≤ (1 + ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)) := by sorry

end EffResSparsify.Sampling
