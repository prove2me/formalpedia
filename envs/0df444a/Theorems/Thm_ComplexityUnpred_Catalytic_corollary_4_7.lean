-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_corollary_4_7
-- name    : ComplexityUnpred.Catalytic.corollary_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:03:39.394568+00:00
-- url     : https://prove2.me/theorems/ca360c6e-4742-4a81-a8a9-ccabfcc0f2e1
-- title:
--   Corollary 4.7 — a multiset with advantage below 1/2^{ℓ+1} against P(G) contains a WeakExcess solution
-- statement:
--   Let $G$ be a deterministic hypercube digraph of dimension $n$ with $\ell$-bit labels and $\mathcal P(G)$ its predictors (Definition 4.5). If $S\subseteq\{0,1\}^n$ is a non-empty multiset with
--   $$\mathrm{adv}_{U(S)}(\mathcal P(G))<\frac1{2^{\ell+1}},$$
--   then $S$ contains a solution to WeakExcess on $G$: some $s\in S$ has $\text{out-degree}_G(s)\ge\text{in-degree}_G(s)$.
--
--   This is the correctness of the reduction WeakExcess $\le_P$ UNPRED (Theorem 4.8), with $\epsilon=1/2^{\ell+1}$.
--
--   **Formalization Note** `advFam S G.predictors` is $\mathrm{adv}_{U(S)}(\mathcal P(G))$, the maximum over the $2^{\ell+1}$ predictors.
--
--   Differences from the source:
--   - generalization: n, ℓ ∈ ℕ = {1, 2, …} → n ℓ : ℕ, ℓ = 0 allowed; reason: covers every n, ℓ ≥ 1
--   - encoding: strings in {0,1}ⁿ, indices in [n] = {1, …, n} → Fin n → Bool, 0-based indices Fin n; reason: Lean convention; same instances
--   - encoding: G = (V, E, lab, ind) with E a multiset and lab : E → {0,1}^ℓ → HypercubeDigraph n ℓ: a Multiset of (tail, head, label) triples and ind; reason: Lean convention; same multigraphs
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 32, Corollary 4.7

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_WeakExcess

namespace ComplexityUnpred.Catalytic

/-- **Corollary 4.7** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 32). If `G` is a deterministic
hypercube digraph of dimension `n` with `ℓ`-bit labels and `S ⊆ {0,1}ⁿ` is a non-empty multiset
with `adv_{U(S)}(P(G)) < 1/2^{ℓ+1}`, then `S` contains a solution to WeakExcess on `G`: a vertex
`s` with `out-degree_G(s) ≥ in-degree_G(s)`. -/
theorem corollary_4_7 {n ℓ : ℕ} (G : HypercubeDigraph n ℓ) (hG : G.IsDeterministic)
    (S : Multiset (Fin n → Bool)) (hS : S ≠ 0)
    (hadv : advFam S G.predictors < 1 / 2 ^ (ℓ + 1)) :
    ∃ s ∈ S, G.inDeg s ≤ G.outDeg s := by sorry

end ComplexityUnpred.Catalytic
