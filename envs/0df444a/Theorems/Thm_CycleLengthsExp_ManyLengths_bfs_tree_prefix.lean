-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_bfs_tree_prefix
-- name    : CycleLengthsExp.ManyLengths.bfs_tree_prefix
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-16T12:00:20.526657+00:00
-- url     : https://prove2.me/theorems/d29973fb-61c8-4be2-92a6-bace95a8772a
-- title:
--   Theorem 2 proof — BFS tree prefix with the last-two-levels frontier property
-- statement:
--   The BFS tree prefix opening the proof of Theorem 2 (Friedman and Krivelevich, *Cycle lengths in expanding graphs*, p. 13: "Run the BFS algorithm ... until a tree T of size exactly ⌊αn/4⌋ is obtained").
--
--   Let $0<\alpha\le 1$ with $\alpha n \ge 12$, and let $G$ be an $\alpha$-expander on $n$ vertices. Then there is a vertex set $S$ with $|S| = \lfloor \alpha n/4 \rfloor$ that is the vertex set of a subtree $T$ of $G$, rooted at $v_0 \in S$, such that $T$ is acyclic, every vertex of $S$ is reachable from $v_0$ in $T$, every vertex of $S$ has level at most $m$ in $T$, some vertex attains level $m$, and — the load-bearing property — every neighbour $q \notin S$ of a vertex $t \in S$ satisfies $m - 1 \le \mathrm{level}_T(v_0, t)$: neighbours outside $S$ touch only the last two levels of $T$.
--
--   This holds because $S$ is a PREFIX of a full BFS tree (all of levels $1,\dots,m-1$ plus some of level $m$): a vertex $t$ at level $\le m-2$ has every neighbour at level $\le m-1$, hence inside $S$. A bare "some tree of size $\lfloor\alpha n/4\rfloor$" does NOT imply this frontier property; the proof must build $T$ as such a prefix.
--
--   On PUBLISHED this unblocks the PROVE of the BFS prefix node, then the tree-extension/attachment node and the branch-cycles node, and hence the assembly of Theorem 2 itself.
--
--   Parent `CycleLengthsExp.ManyLengths.theorem_2` (`3ede001e-4457-441c-8fe4-434ac2135ff1`) live-verified Open with `deprecated_at=null` immediately before posting; no duplicate `bfs_tree_prefix` node exists in the mission (mission-list checked 2026-10-16).
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 13, proof of Theorem 2, paragraph beginning 'Run the BFS algorithm'

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- BFS tree prefix (Friedman–Krivelevich, p. 13: "Run the BFS algorithm ...
until a tree T of size exactly ⌊αn/4⌋ is obtained").

`S` is the vertex set of a PREFIX of a full BFS tree (all of levels `1..m-1`
plus some of level `m`), rooted at `v₀`. The load-bearing property is
`hTfront`: neighbours outside `S` only touch the last two levels of `T`.
It holds because a vertex `t` at level `≤ m-2` has every neighbour at level
`≤ m-1`, hence inside `S`. A bare "some tree of size ⌊αn/4⌋" does NOT
imply `hTfront`; the future proof must build `T` as such a prefix. -/
theorem bfs_tree_prefix (n : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) :
    ∃ (S : Set (Fin n)) (T : G.Subgraph) (v₀ : Fin n) (m : ℕ),
      S.ncard = Nat.floor (α * (n : ℝ) / 4) ∧
      T.verts = S ∧
      v₀ ∈ S ∧
      T.spanningCoe.IsAcyclic ∧
      (∀ v ∈ S, T.spanningCoe.Reachable v₀ v) ∧
      (∀ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v ≤ m) ∧
      (∃ v ∈ S, CycleLengthsExp.WellSpread.level T v₀ v = m) ∧
      (∀ t ∈ S, ∀ q : Fin n, q ∉ S → G.Adj t q →
        m - 1 ≤ CycleLengthsExp.WellSpread.level T v₀ t) := by
  sorry

end CycleLengthsExp.ManyLengths
