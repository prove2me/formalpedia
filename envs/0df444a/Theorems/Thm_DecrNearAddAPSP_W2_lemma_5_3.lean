-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_5_3
-- name    : DecrNearAddAPSP.W2.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:11:11.289306+00:00
-- url     : https://prove2.me/theorems/24e50d5d-efce-4b45-be29-7dbe79e9cc9b
-- title:
--   Lemma 5.3 — over a deletion sequence, E_S(u) ever holds O(α/q) edges in expectation
-- statement:
--   Let $G_0$ have positive integer weights and let $G_0,\dots,G_T$ be produced by a sequence of edge deletions. Let $S\subseteq V$ be formed by selecting each vertex independently with probability $q\in(0,1)$, fix a vertex $u$, and let $\alpha\in\mathbb N$ be such that, for every outcome of $S$, $\delta_{G_t}(u,S)$ changes at most $\alpha$ times over $t=0,\dots,T$. Write $N_S(u)$ for the number of distinct edges $(u,v)$ that lie in $E_S(u)$ of $G_t$ for some $t$. There is a universal constant $C$ (independent of $n$, $G_0$, the sequence, $q$, $u$ and $\alpha$) such that
--   $$
--   \mathbb E_S\big[N_S(u)\big]\ \le\ C\,\frac{\alpha}{q}+C .
--   $$
--
--   This bounds the cumulative size of the decremental hierarchy-induced edge set at one vertex; Corollary 5.4 sums it over the vertices, which is what makes the Monotone ES-trees on $E_S$ cheap. As printed the bound misses the edges already in $E_S(u)$ at time $0$, about $1/q$ of them, and fails at $\alpha=0$ (a star with weights $1,\dots,n-1$, no deletions, small $q$); the statement is posed as printed.
--
--   Differences from the source:
--
--   - reading: a graph G = (V, E) (Lemma statement); §5 p. 25: "each edge e ∈ E has a positive weight w(e) > 0" → G.PosWeights (every edge weight ≥ 1); reason: standing assumption of the weighted sections (§5 p. 25), with integer weights (p. 6)
--   - reading: the total number of edges in E_S(u) throughout all edge deletions is O(α/q) → E_S[#distinct edges ever in E_S(u), initial members included] ≤ C·α/q + C for a universal C; reason: 'expected' is omitted on the page but the proof and Corollary 5.4 bound an expectation; O(·) is an explicit constant fixed before the instance, with an additive C
--   - reading: the maximal number of distance updates between a vertex u ∈ V and S is α → for every outcome S, the number of t < T with δ_{t+1}(u, S) ≠ δ_t(u, S) is ≤ α; reason: α is a deterministic bound over all outcomes of S; ≤ α is equivalent to 'the maximum is α' since the bound is monotone in α
--   - encoding: S formed by selecting each vertex independently with probability q → the expectation Σ_S q^{|S|}(1 − q)^{n−|S|}·X(S), 0 < q < 1; reason: the law of independent sampling as a finite sum; q ∈ (0, 1) as on p. 26
--   - encoding: vertex set V, distances δ → V = Fin n; δ in ℕ∞ (∞ = no path); reason: Lean convention; same instances
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 26, Lemma 5.3

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_Sampling

namespace DecrNearAddAPSP.W2

/-- **Lemma 5.3** (p. 26). There is a universal constant `C` such that: for every graph `G_0` with
positive weights, every deletion sequence, every `q ∈ (0, 1)`, every vertex `u` and every `α ∈ ℕ`
bounding, for every outcome of `S`, the number of distance updates between `u` and `S`, the expected
number of edges ever in `E_S(u)` (over `S` formed by selecting each vertex independently with
probability `q`) is at most `C·α/q + C`. -/
theorem lemma_5_3 : ∃ C : ℝ, ∀ (n : ℕ) (G₀ : WGraph (Fin n)) (σ : List (Upd n)) (q : ℝ)
    (u : Fin n) (α : ℕ), G₀.PosWeights → IsDelSeq G₀ σ → 0 < q → q < 1 →
    (∀ S : Finset (Fin n), distUpdates G₀ σ S u ≤ α) →
    sampleExp q (fun S => (everInHier G₀ σ S u : ℝ)) ≤ C * α / q + C := by sorry

end DecrNearAddAPSP.W2
