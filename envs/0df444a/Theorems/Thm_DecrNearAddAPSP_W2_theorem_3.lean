-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_theorem_3
-- name    : DecrNearAddAPSP.W2.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:11:14.487196+00:00
-- url     : https://prove2.me/theorems/6a356fa5-2556-4e84-885e-ad757bcfb9e5
-- title:
--   Theorem 3 — decremental (1+ε, 2W₂)-APASP under deletions and weight increases in expected Õ(n^{3/2}m^{1/2}) total update time
-- statement:
--   **Setting.** Algorithms run on the word RAM with $a\lceil\log_2(n+2)\rceil$-bit words and uniform random words (`DynBrooks_Machine`). A program receives $n$, $W$, $m$ and the $m$ edges of $G_0$, then the updates one at a time, and maintains a distance matrix $d$ by writing records replayed from $d[u,u]=0$, $d[u,v]=\infty$; its total update time $T$ counts every step from the start through the completed state after the last update. For a path $\pi$, $W_2(\pi)$ is its second-largest edge weight ($0$ with fewer than two edges).
--
--   **Theorem.** For every $\varepsilon>0$ and every weight exponent $c_W\ge1$ there are one program $P$, a word-size constant $a$, a function $f:\mathbb N\to\mathbb R$ with $f(n)\to0$ and a constant $C$ such that, for every $n\ge2$, every graph $G_0$ on $\{0,\dots,n-1\}$ with $m$ edges and integer weights in $[1,W]$, $W\le n^{c_W}$, and every sequence of edge deletions and strict weight increases (weights at most $W$) fixed before the coin tape:
--
--   1. on every coin tape, at time $0$ and after every update $t$ (whenever that completed state is reached), for all $u,v$:
--   $$
--   \delta_t(u,v)\ \le\ d_t[u,v]\ \le\ (1+\varepsilon)\,\delta_t(u,v)+2\,W_2(\pi)\quad\text{for every shortest $u$–$v$ path $\pi$ of $G_t$};
--   $$
--   2. $\mathbb E[T]\le C\,n^{3/2+f(n)}\,m^{1/2}+C$;
--   3. for every $c>0$ there is $C_c$ such that $\mathbb E[T]\le C_c\,n^{3/2}\,m^{1/2}(\log_2 n)^{C_c}+C_c$ whenever $m\ge n^{1+c}$.
--
--   This is the paper's first result for weighted graphs: a near-additive stretch whose additive term $2W_2$ is local to the pair, in the total update time of the $(2+\varepsilon)$-approximation of Dory, Forster, Nazari and de Vos. As printed it is false: the bound has no term for the number of updates, while unit weight increases from $1$ to $n$ on $K_n$ give about $n^3/2$ legal updates, each of which costs at least the steps that read it. The statement is posed as printed.
--
--   Differences from the source:
--
--   - encoding: an algorithm (no machine named); 'maintains a distance estimate' → one program on DynBrooks_Machine with words of a·⌈log₂(n+2)⌉ bits; input n, W, m, the edges u, v, w(uv), updates 0, u, v (delete) and 1, u, v, c (increase to c); d_t the replay of records u, v, q (q = 0 ↦ ∞, q ↦ q − 1) from d[u, u] = 0, d[u, v] = ∞; reason: the standard word RAM; writing records makes the estimate part of the run, and the defaults spare a forced n-word write when m = 0
--   - encoding: d[u, v] a distance estimate → d_t[u, v] ∈ ℕ ∪ {∞}; reason: δ_t is an integer, so ⌊d⌋ satisfies both bounds whenever d does
--   - encoding: expected total update time → the lower Lebesgue integral over the coin-tape law of T ∈ ℕ∞, T counting initialization and every update (reads included) until the completed state after the last update; reason: every executed instruction is one step; a run that never completes has T = ∞
--   - reading: Õ(n^{3/2}m^{1/2}) when m = n^{1+Ω(1)} → for every c > 0 there is C_c with E[T] ≤ C_c·n^{3/2}·m^{1/2}·(log₂ n)^{C_c} + C_c on every instance with m ≥ n^{1+c}; reason: Ω(1) is a fixed positive exponent c; Õ hides a polylog n factor; constants fixed before the instance
--   - reading: Õ(n^{3/2+o(1)}m^{1/2}) otherwise → one f with f(n) → 0 and C with E[T] ≤ C·n^{3/2+f(n)}·m^{1/2} + C on every instance; reason: the o(1) is one function of n fixed with the program; polylog factors are absorbed into it; holding on every instance is the stronger reading
--   - reading: (1 + ε, 2W₂)-APASP, W₂ 'the weight of the 2nd heaviest edge on any shortest path in the current graph' (abstract) → δ_t ≤ d_t and d_t ≤ (1 + ε)·w(π) + 2·W₂(π) for every shortest path π of G_t (a simple path with w(π) = δ_t); reason: 'any' read universally, as Lemma 7.1 (every simple path) delivers
--   - reading: the algorithm maintains the estimate (randomized, oblivious adversary) → the bounds hold on every coin tape at every completed state that is reached, for a sequence fixed before the tape; reason: the stretch analysis (Lemma 7.1) is deterministic given the sample
--   - reading: integer weights, W_max ∈ O(n^{O(1)}) (p. 6, footnote 3) → for every c_W ≥ 1 fixed before the program: weights integers in [1, W] with W ≤ n^{c_W}; reason: the standing assumption; constants and the program may depend on c_W and ε
--   - encoding: n vertices, m edges → n ≥ 2, V = Fin n, m = |E(G_0)|; an additive constant C in both time bounds; reason: log₂ n > 0 for n ≥ 2; the additive constant covers instances with m = 0
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 5, Theorem 3 (restated p. 48)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_Run
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DecrNearAddAPSP.W2

/-- **Theorem 3** (p. 5; restated p. 48). For every `ε > 0` and every weight exponent `c_W ≥ 1`
there are one word-RAM program `P`, a word-size constant `a`, a function `f` with `f(n) → 0` and a
constant `C` such that, for every `n ≥ 2`, every graph `G_0` on `Fin n` with `m` edges and integer
weights in `[1, W]`, `W ≤ n^{c_W}`, and every sequence of edge deletions and weight increases fixed
before the coin tape:
1. on every coin tape, at time `0` and after every update `t` (when that completed state is
   reached), the maintained estimate satisfies `δ_t(u, v) ≤ d_t[u, v]` and, for every shortest
   `u`–`v` path `π` of `G_t`, `d_t[u, v] ≤ (1 + ε)·δ_t(u, v) + 2·W_2(π)`;
2. the expected total update time is at most `C·n^{3/2 + f(n)}·m^{1/2} + C`;
3. for every `c > 0` there is `C_c` such that the expected total update time is at most
   `C_c·n^{3/2}·m^{1/2}·(log₂ n)^{C_c} + C_c` whenever `m ≥ n^{1+c}`. -/
theorem theorem_3 : ∀ ε : ℝ, 0 < ε → ∀ cW : ℝ, 1 ≤ cW →
    ∃ (P : DynBrooks.Program) (a : ℕ) (f : ℕ → ℝ) (C : ℝ), Tendsto f atTop (𝓝 0) ∧
    (∀ (n W : ℕ) (G₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) (σ : List (Upd n)),
      2 ≤ n → (W : ℝ) ≤ (n : ℝ) ^ cW → IsDecrInstance W G₀ σ → IsEdgeListing G₀ es →
      (∀ (ω : ℕ → BitVec (wordSize a n)) (t : ℕ), t ≤ σ.length →
        (stateAt P ω (apspInitWords W G₀ es) (σ.map Upd.words) t).isSome →
        ∀ u v : Fin n, (graphAt G₀ σ t).dist u v ≤ estAt P ω W G₀ es σ t u v ∧
          ∀ π : (graphAt G₀ σ t).adj.Walk u v, (graphAt G₀ σ t).IsShortestPath π →
            estAt P ω W G₀ es σ t u v ≠ ⊤ ∧
            ((estAt P ω W G₀ es σ t u v).toNat : ℝ) ≤
              (1 + ε) * ((graphAt G₀ σ t).walkWeight π : ℝ) +
                2 * ((graphAt G₀ σ t).heavy π 2 : ℝ)) ∧
      ∫⁻ ω, (apspTime P ω W G₀ es σ : ℝ≥0∞) ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ ((3 : ℝ) / 2 + f n) *
          (G₀.adj.edgeSet.ncard : ℝ) ^ ((1 : ℝ) / 2) + C)) ∧
    (∀ c : ℝ, 0 < c → ∃ Cc : ℝ,
      ∀ (n W : ℕ) (G₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) (σ : List (Upd n)),
      2 ≤ n → (W : ℝ) ≤ (n : ℝ) ^ cW → IsDecrInstance W G₀ σ → IsEdgeListing G₀ es →
      (n : ℝ) ^ (1 + c) ≤ (G₀.adj.edgeSet.ncard : ℝ) →
      ∫⁻ ω, (apspTime P ω W G₀ es σ : ℝ≥0∞) ∂(DynBrooks.coinMeasure (wordSize a n)) ≤
        ENNReal.ofReal (Cc * (n : ℝ) ^ ((3 : ℝ) / 2) *
          (G₀.adj.edgeSet.ncard : ℝ) ^ ((1 : ℝ) / 2) * log2 n ^ Cc + Cc)) := by sorry

end DecrNearAddAPSP.W2
