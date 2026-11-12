-- Prove2me | Theorems.Thm_DecrNearAddAPSP_W2_lemma_2_5
-- name    : DecrNearAddAPSP.W2.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:13:07.388357+00:00
-- url     : https://prove2.me/theorems/7dfd4b42-6563-4721-9158-f49aee9500a7
-- title:
--   Lemma 2.5 [HKN15] — a monotone ES-tree up to level τ runs in Õ(E(H)·τ + W(H) + n) total update time
-- statement:
--   For every weight exponent $c_W\ge1$ there are a word-RAM program $P$, a word-size constant $a$ and a constant $C$ with the following property. Let $n\ge1$, $s$ a root, $\tau$ a depth with $1\le\tau\le n^{c_W}$, $W\le n^{c_W}$, $H_0$ a graph on $\{0,\dots,n-1\}$ with integer weights in $[1,W]$ given by an edge listing, and let $H$ undergo any sequence of edge insertions (with weights in $[1,W]$), edge deletions and weight increases (to at most $W$). Then on every coin tape:
--
--   1. at every time $t$ the replay of the level records $P$ has written equals the monotone ES-tree levels $\ell_t$ of $H$ rooted at $s$ up to level $\tau$;
--   2. the total update time $T$ satisfies
--   $$
--   T\ \le\ C\,\big(E(H)\cdot\tau+W(H)+n\big)\,(\log_2 n)^{C}+C,
--   $$
--   where $E(H)$ is the number of edges ever contained in $H$ and $W(H)$ the number of updates to $H$.
--
--   This is the running-time guarantee for the Monotone ES-trees maintained by Algorithm 3 and Algorithm 4, which the total update time of the goal is assembled from.
--
--   Differences from the source:
--
--   - encoding: a monotone ES-tree on a graph H (no machine named) → one program on the published word RAM DynBrooks_Machine with words of a·⌈log₂(n+2)⌉ bits; input n, s, τ, |E(H_0)|, the edges, then update words; level records v, q replayed from all-∞; reason: the paper's computational model is the standard word RAM; the records make 'maintains ℓ' a property of the program
--   - encoding: total update time → steps of initialization and of every update, reads included, in ℕ∞; reason: every executed instruction is one step; ∞ if a run does not complete
--   - reading: Õ(E(H)·τ + W(H) + n) → ≤ C·(E(H)·τ + W(H) + n)·(log₂ n)^C + C, C depending only on c_W; reason: Õ hides polylog n factors; the additive C covers n = 1
--   - reading: the bound holds (a deterministic data structure; no expectation on the page) → the replay and the time bound hold on every coin tape; reason: the lemma states a total update time, not an expected one
--   - reading: polynomial weights (p. 6, footnote 3) and τ ≤ nW_max (p. 27) → W ≤ n^{c_W} and τ ≤ n^{c_W}, for every c_W ≥ 1 fixed before the program; reason: the standing assumption W_max ∈ O(n^{O(1)}) with the depth range the paper uses; quantifying over every c_W covers every polynomial bound
--   - reading: H undergoing edge deletions, insertions, and weight increases → insertions of a new edge with weight in [1, W]; deletions of a present edge; increases of a present edge's weight to c ≤ W; reason: positive integer weights as in the weighted sections; the update kinds as listed
--   - reading: E(H) the total number of edges ever contained in H → the number of distinct vertex pairs {x, y} that are an edge of some H_t, 0 ≤ t ≤ |ρ|; reason: an edge deleted and later re-inserted is the same edge of H; this is the smaller count, so the bound is the stronger of the two readings, and each re-insertion is still paid for by W(H)
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 8, Lemma 2.5

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_Run
import Definitions.Def_DecrNearAddAPSP_W2_MonoES
open scoped ENNReal

namespace DecrNearAddAPSP.W2

/-- **Lemma 2.5** ([HKN15], p. 8). For every weight exponent `c_W ≥ 1` there are a word-RAM program,
a word-size constant `a` and a constant `C` such that: for every `n`, root `s`, depth
`1 ≤ τ ≤ n^{c_W}`, weight bound `W ≤ n^{c_W}`, initial graph `H_0` with weights in `[1, W]` (given
by an edge listing) and every sequence of edge insertions, deletions and weight increases of `H`
(weights in `[1, W]`), on every coin tape the program's level records replay to the monotone
ES-tree levels `ℓ_t` of `H` rooted at `s` up to level `τ` at every time `t`, and its total update
time is at most `C·(E(H)·τ + W(H) + n)·(log₂ n)^C + C`, where `E(H)` is the number of edges ever in
`H` and `W(H)` the number of updates. -/
theorem lemma_2_5 : ∀ cW : ℝ, 1 ≤ cW → ∃ (P : DynBrooks.Program) (a : ℕ) (C : ℝ),
    ∀ (n W τ : ℕ) (s : Fin n) (H₀ : WGraph (Fin n)) (es : List (Fin n × Fin n))
      (ρ : List (ESUpd n)),
      1 ≤ τ → (τ : ℝ) ≤ (n : ℝ) ^ cW → (W : ℝ) ≤ (n : ℝ) ^ cW → H₀.WeightsIn W →
      IsLegalESSeq W H₀ ρ → IsEdgeListing H₀ es →
      ∀ ω : ℕ → BitVec (wordSize a n),
        (∀ t ≤ ρ.length, levelsAt P ω s τ H₀ es ρ t =
          monoLevels (fun t => (esGraphAt H₀ ρ t).toD) s τ t) ∧
        (esTime P ω s τ H₀ es ρ : ℝ≥0∞) ≤
          ENNReal.ofReal (C * ((everEdges H₀ ρ : ℝ) * τ + ρ.length + n) * log2 n ^ C + C) := by sorry

end DecrNearAddAPSP.W2
