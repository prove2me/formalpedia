-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_theorem_1
-- name    : EffResSparsify.Sampling.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:23.821984+00:00
-- url     : https://prove2.me/theorems/311eec0b-39b3-4730-85c6-b5c0f36205e7
-- title:
--   Theorem 1 — Sparsify$(G,q)$ with $q=9C^2n\log n/\varepsilon^2$ is a $(1\pm\varepsilon)$ spectral sparsifier with probability $\ge 1/2$
-- statement:
--   There are an absolute constant $C>0$ and a threshold $N_0$ such that the following holds for every $n\ge N_0$. Let $G=(V,E,w)$ be a connected weighted graph on $n$ vertices with positive edge weights and Laplacian $L$, and let $1/\sqrt n<\varepsilon\le1$. Let
--   $$q=\Big\lceil\frac{9C^2\,n\log n}{\varepsilon^2}\Big\rceil$$
--   and let $H=\mathrm{Sparsify}(G,q)$, with Laplacian $\tilde L$: $q$ edges are drawn independently with replacement, edge $e$ with probability $p_e$ proportional to $w_eR_e$ (its weight times its effective resistance), and each draw of $e$ adds weight $w_e/(qp_e)$ to $e$ in $H$. Then with probability at least $1/2$,
--   $$\forall x\in\mathbb R^n:\qquad(1-\varepsilon)\,x^{\mathsf T}Lx\le x^{\mathsf T}\tilde Lx\le(1+\varepsilon)\,x^{\mathsf T}Lx.$$
--
--   This is the main theorem of the paper: every weighted graph has a spectral sparsifier with $O(n\log n/\varepsilon^2)$ edges, obtained by independent sampling according to effective resistances.
--
--   **Formalization Note** The paper's "$C$ is the constant in Lemma 5" and "$n$ sufficiently large" are quantified as $\exists C>0,\ \exists N_0,\ \forall n\ge N_0$, before the graph, the edge type and $\varepsilon$, so both are uniform over all graphs and all admissible $\varepsilon$. The printed $q=9C^2n\log n/\varepsilon^2$ is not an integer and is rounded up. $\log$ is natural. Vertices are `Fin n`; the edge set is any finite type with an arbitrary orientation and no loops (parallel edges allowed). Probability is the finite sum over the $|E|^q$ outcomes of $\prod_i p_{s_i}$ times the indicator of the event.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 2, Theorem 1 (proof pp. 8–9)

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs

namespace EffResSparsify.Sampling

open Matrix

/-- Theorem 1, p. 2: there are an absolute constant `C > 0` and a threshold `N₀` such that for
every `n ≥ N₀`, every connected weighted graph `G` on `n` vertices and every
`1/√n < ε ≤ 1`, with `q = ⌈9 C² n log n / ε²⌉`, the graph `H = Sparsify(G, q)` satisfies
`(1 − ε) xᵀ L x ≤ xᵀ L̃ x ≤ (1 + ε) xᵀ L x` for all `x ∈ ℝⁿ` with probability at least `1/2`. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (E : Type) [Fintype E] [DecidableEq E] (G : WGraph (Fin n) E), G.IsConnected →
      ∀ ε : ℝ, 1 / Real.sqrt n < ε → ε ≤ 1 →
        (1 / 2 : ℝ) ≤ G.sparsifyProb ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊
          (fun s => ∀ x : Fin n → ℝ,
            (1 - ε) * (x ⬝ᵥ (G.laplacian *ᵥ x)) ≤
                x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ∧
              x ⬝ᵥ (G.sparsifiedLaplacian ⌈9 * C ^ 2 * n * Real.log n / ε ^ 2⌉₊ s *ᵥ x) ≤
                (1 + ε) * (x ⬝ᵥ (G.laplacian *ᵥ x))) := by sorry

end EffResSparsify.Sampling
