-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_lemma_4_6
-- name    : ComplexityUnpred.Catalytic.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:03:28.853502+00:00
-- url     : https://prove2.me/theorems/f9f6a7e0-474b-4480-b93a-efda34b5534c
-- title:
--   Lemma 4.6 — exact success rate of the predictors P(G) of a deterministic hypercube digraph
-- statement:
--   Let $G=(V,E,\mathrm{lab},\mathrm{ind})$ be a deterministic hypercube digraph of dimension $n$ with $\ell$-bit labels, and let $\mathcal P(G)=(P_{lj}(G))_{l\in\{0,1\}^\ell,j\in\{0,1\}}$ be its family of $2^{\ell+1}$ middle-bit predictors (Definition 4.5). For every string $s\in\{0,1\}^n$,
--   $$\Pr_{l\in\{0,1\}^\ell,\ j\in\{0,1\}}\big[P_{lj}(G)\text{ succeeds on }s\big]=\frac12+\frac{\text{in-degree}_G(s)-\text{out-degree}_G(s)}{2^{\ell+1}},$$
--   where $(l,j)$ is uniform on $\{0,1\}^\ell\times\{0,1\}$ and degrees count edge copies (a self-loop adds $1$ to both).
--
--   The identity converts the predictive power of $\mathcal P(G)$ on a vertex into its degree imbalance, which is how WeakExcess is reduced to UNPRED.
--
--   **Formalization Note** `famProb` over the index type `(Fin ℓ → Bool) × Bool` is the uniform probability over $(l,j)$; the equality is exact, in $\mathbb R$.
--
--   Differences from the source:
--   - generalization: n, ℓ ∈ ℕ = {1, 2, …} → n ℓ : ℕ, ℓ = 0 allowed (n = 0 admits no hypercube digraph); reason: covers every n, ℓ ≥ 1
--   - encoding: strings in {0,1}ⁿ, indices in [n] = {1, …, n} → Fin n → Bool, 0-based indices Fin n; reason: Lean convention; same instances
--   - encoding: G = (V, E, lab, ind) with E a multiset and lab : E → {0,1}^ℓ → HypercubeDigraph n ℓ: a Multiset of (tail, head, label) triples and ind; reason: Lean convention; same multigraphs
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 32, Lemma 4.6

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_WeakExcess

namespace ComplexityUnpred.Catalytic

/-- **Lemma 4.6** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 32). For a deterministic hypercube
digraph `G` of dimension `n` with `ℓ`-bit labels and every `s ∈ {0,1}ⁿ`,
`Pr_{l ∈ {0,1}^ℓ, j ∈ {0,1}}[P_{lj}(G) succeeds on s]
  = 1/2 + (in-degree_G(s) − out-degree_G(s)) / 2^{ℓ+1}`. -/
theorem lemma_4_6 {n ℓ : ℕ} (G : HypercubeDigraph n ℓ) (hG : G.IsDeterministic)
    (s : Fin n → Bool) :
    famProb (fun p : (Fin ℓ → Bool) × Bool => (G.predictors p).succeeds) s =
      1 / 2 + ((G.inDeg s : ℝ) - (G.outDeg s : ℝ)) / 2 ^ (ℓ + 1) := by sorry

end ComplexityUnpred.Catalytic
