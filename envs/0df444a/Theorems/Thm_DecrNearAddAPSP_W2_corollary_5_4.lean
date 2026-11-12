-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_corollary_5_4
-- name    : DecrNearAddAPSP.W2.corollary_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:11:24.049254+00:00
-- url     : https://prove2.me/theorems/b0a0b1f1-5f51-493a-b4c3-ca8ffc462d34
-- title:
--   Corollary 5.4 — summed over all vertices, E_S ever holds O(αn/q) edge-vertex incidences in expectation
-- statement:
--   Under the setting of Lemma 5.3 (positive integer weights, a deletion sequence, $S$ sampled with probability $q\in(0,1)$), let $\alpha\in\mathbb N$ bound, for every outcome of $S$ and every vertex $u$, the number of times $\delta(u,S)$ changes over the sequence. With $N_S(u)$ the number of distinct edges ever in $E_S(u)$, there is a universal constant $C$ such that
--   $$
--   \mathcal E_S:=\mathbb E_S\Big[\sum_{u\in V}N_S(u)\Big]\ \le\ C\,\frac{\alpha n}{q}+C .
--   $$
--
--   Applied with $\alpha=\tau$ to the bounded set $E^\tau_S$, it gives the $O(n\tau/q)$ cumulative size that bounds the Monotone ES-trees of Algorithm 3. As printed it fails at $\alpha=0$ for the same reason as Lemma 5.3; the statement is posed as printed.
--
--   Differences from the source:
--
--   - reading: a graph G = (V, E) (Lemma statement); §5 p. 25: "each edge e ∈ E has a positive weight w(e) > 0" → G.PosWeights (every edge weight ≥ 1); reason: standing assumption of the weighted sections (§5 p. 25), with integer weights (p. 6)
--   - reading: the expected total number of edge-vertex incidences ever inserted into E_S throughout all edge deletions is O(αn/q) → E_S[Σ_u #distinct edges ever in E_S(u)] ≤ C·α·n/q + C, C universal; reason: 'ever inserted' is read as 'ever present' (initial members included), as Corollary 5.5(3) and Lemma 5.9 use it; O(·) is an explicit constant with an additive C
--   - reading: α the maximum number of times δ(u, S) increases over all edge deletions, over all u ∈ V → for every outcome S and every u, #{t < T : δ_{t+1}(u, S) ≠ δ_t(u, S)} ≤ α; reason: under deletions δ(u, S) never decreases, so changes are increases; ≤ α is equivalent to 'the maximum is α'
--   - encoding: S formed by selecting each vertex independently with probability q → the expectation Σ_S q^{|S|}(1 − q)^{n−|S|}·X(S), 0 < q < 1; reason: the law of independent sampling as a finite sum
--   - encoding: vertex set V, distances δ → V = Fin n; δ in ℕ∞ (∞ = no path); reason: Lean convention; same instances
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 27, Corollary 5.4

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_Sampling

namespace DecrNearAddAPSP.W2

/-- **Corollary 5.4** (p. 27). There is a universal constant `C` such that: for every graph `G_0`
on `n` vertices with positive weights, every deletion sequence, every `q ∈ (0, 1)` and every
`α ∈ ℕ` bounding, for every outcome of `S` and every vertex `u`, the number of times `δ(u, S)`
changes, the expected total number of edge-vertex incidences ever in `E_S`,
`E_S[Σ_u #edges ever in E_S(u)]`, is at most `C·α·n/q + C`. -/
theorem corollary_5_4 : ∃ C : ℝ, ∀ (n : ℕ) (G₀ : WGraph (Fin n)) (σ : List (Upd n)) (q : ℝ)
    (α : ℕ), G₀.PosWeights → IsDelSeq G₀ σ → 0 < q → q < 1 →
    (∀ (S : Finset (Fin n)) (u : Fin n), distUpdates G₀ σ S u ≤ α) →
    sampleExp q (fun S => ∑ u : Fin n, (everInHier G₀ σ S u : ℝ)) ≤ C * α * n / q + C := by sorry

end DecrNearAddAPSP.W2
