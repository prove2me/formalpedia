-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_theorem_5_4
-- name    : ConstrainedDirSep.STSep.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:07:44.335223+00:00
-- url     : https://prove2.me/theorems/31b7bddf-1be1-4f57-a131-a5c8e1ba329a
-- title:
--   Theorem 5.4 — deterministic directed flow augmentation (cited from Kim, Kratsch, Pilipczuk, Wahlström)
-- statement:
--   There are a constant $C$ and a deterministic multi-stack Turing machine $M$ such that the following holds. Let $G$ be a directed graph on $\{0,\dots,n_V-1\}$ (no parallel arcs) whose arcs have capacities in $\{1,+\infty\}$, let $s,t$ be vertices and $k\ge0$. On input $(G,s,t,k)$, $M$ halts within $C\cdot2^{C k^4\log k}\cdot(n_V+1)^C$ steps and outputs a family $\mathcal A$ of sets $A\subseteq V(G)\times V(G)$ with
--   $$|\mathcal A|\le C\cdot 2^{C k^4\log k}\cdot(\log n_V)^{C k^3},$$
--   such that for every inclusion-minimal $s$–$t$ arc cut $Z\subseteq A(G)$ of value at most $k$ there is $A\in\mathcal A$ for which $Z$ is a minimum $s$–$t$ cut in $G+A$. Here $G+A$ adds, for every ordered pair in $A$, one infinite-capacity arc with that tail and head, in parallel to any arc of $G$ already joining the pair, and $\log x=\log_2\max\{x,2\}$.
--
--   The paper cites this from Kim, Kratsch, Pilipczuk and Wahlström (2025, Theorem 1.2) and applies it to the split graph.
--
--   Differences from the source:
--   - reading: "a directed graph G whose arcs have capacities in {1, +∞}" → G without parallel arcs, given by a two-bit matrix (arc present, infinite capacity); reason: the running time is bounded in |V(G)| alone, which cannot even read an input with unboundedly many parallel arcs, and the paper applies the theorem to the split graph, which has none.
--   - reading: unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2); reason: the bounds are polynomial in |V(G)| for fixed k, the same in all polynomially equivalent deterministic models.
--   - encoding: 2^{O(k⁴ log k)}|V(G)|^{O(1)} and 2^{O(k⁴ log k)}(log |V(G)|)^{O(k³)} → C·2^{C·k⁴·⌊log₂ max(k, 2)⌋}·(n_V + 1)^C and C·2^{C·k⁴·⌊log₂ max(k, 2)⌋}·⌊log₂ max(n_V, 2)⌋^{C·k³} with one universal C; reason: floors change log₂ by a factor at most 2, absorbed in C.
--   - encoding: the family 𝒜 → a list of pair sets (repetitions allowed) whose length is bounded; reason: a bound on the list length bounds the family's size.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 19 (PDF 22), Theorem 5.4, cited from [KKPW25, Theorem 1.2]

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_Multigraph

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 19 (PDF 22), Theorem 5.4 (Deterministic directed flow augmentation, cited
from [KKPW25, Theorem 1.2]): for a directed graph `G` with arc capacities in `{1, +∞}`, vertices
`s`, `t` and `k ≥ 0`, an algorithm running in time `2^{O(k⁴ log k)} |V(G)|^{O(1)}` outputs a family
`𝒜` of sets of ordered pairs of vertices, of size `2^{O(k⁴ log k)} (log |V(G)|)^{O(k³)}`, such that
every inclusion-minimal s–t arc cut `Z` of value at most `k` is a minimum s–t cut of `G + A` for
some `A ∈ 𝒜`. `log x` is `log₂ max{x, 2}`. -/
theorem theorem_5_4 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (nV : ℕ) (A : Type) (G : CapMultigraph (Fin nV) A), G.toMultigraph.NoParallel →
        ∀ (s t : Fin nV) (k : ℕ),
        ∃ fam : List (Finset (Fin nV × Fin nV)),
          HMBinPacking.OutputsWithin M
            (encCapDigraph G ++ encNat s.val ++ encNat t.val ++ encNat k) (encPairFamily fam)
            (C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * (nV + 1) ^ C) ∧
          fam.length ≤
            C * 2 ^ (C * k ^ 4 * Nat.log 2 (max k 2)) * (Nat.log 2 (max nV 2)) ^ (C * k ^ 3) ∧
          ∀ Z : Finset A, G.toMultigraph.IsMinimalArcCut s t (Z : Set A) →
            G.cutValue Z ≤ (k : ℕ∞) →
            ∃ Aug ∈ fam, (G.augment Aug).IsMinCut s t (Z.map ⟨Sum.inl, Sum.inl_injective⟩) := by sorry

end ConstrainedDirSep.STSep
