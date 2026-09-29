-- Prove2me | Theorems.Thm_ChvatalPolytopes_SeriesParallel_exists_stable_set_and_circuit_cover
-- name    : ChvatalPolytopes.SeriesParallel.exists_stable_set_and_circuit_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:26:48.452608+00:00
-- url     : https://prove2.me/theorems/0060ded1-bbc3-4c86-b940-7927952e89e4
-- title:
--   A stable set $S$ and a spanning subgraph $F$ with $a+b+\sum k c_k=|S|$ (proof of Theorem 7.1)
-- statement:
--   Let $G=(V,E)$ be a finite series-parallel network. Then there are a stable set $S$ of $G$ and a spanning subgraph $F$ of $G$ (same vertex set $V$, $E(F)\subseteq E$) such that
--
--   1. the components of $F$ are isolated vertices, isolated edges and odd circuits, and
--   2. if $F$ includes $a$ isolated vertices, $b$ isolated edges and $c_k$ circuits of length $2k+1$ ($k\ge1$), then
--   $$
--   a+b+\sum_{k\ge1}k\,c_k=|S| .
--   $$
--
--   This combinatorial statement is what the induction in the proof of Theorem 7.1 establishes; $S$ yields the zero–one primal solution, and $F$ the zero–one dual one.
--
--   **Formalization Note** The sum in 2 is written as $\sum_{K}\operatorname{val}(|K|)$ over the connected components $K$ of $F$, with $\operatorname{val}$ from the `CircuitCover` definition file. An odd-circuit component of $F$ need not induce a chordless cycle in $G$, so it need not belong to $Z(G)$; the passage from $F$ to a zero–one dual solution indexed by $Z(G)$ is not part of this statement.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 151, proof of Theorem 7.1, (i)–(ii)

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_ChvatalPolytopes_SeriesParallel_OddCycleLP
import Definitions.Def_ChvatalPolytopes_SeriesParallel_CircuitCover

namespace ChvatalPolytopes.SeriesParallel

open Classical in
/-- Chvátal 1975, p. 151, proof of Theorem 7.1, (i)–(ii): in a series-parallel network `G` there
are a stable set `S` and a spanning subgraph `F` of `G` such that
(i) the components of `F` are isolated vertices, isolated edges and odd circuits, and
(ii) if `F` has `a` isolated vertices, `b` isolated edges and `c_k` circuits of length `2k + 1`,
then `a + b + ∑ k c_k = |S|`.

`F` is a spanning subgraph: a graph on the same vertex set `V` with `F ≤ G`. The sum in (ii) is
written as the sum over the components of `F` of `componentValue |component|`. -/
theorem exists_stable_set_and_circuit_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G) :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      ∃ F : SimpleGraph V, F ≤ G ∧
        (∀ c : F.ConnectedComponent, IsVertexEdgeOrOddCircuit F c.supp) ∧
        ∑ c : F.ConnectedComponent, componentValue (Fintype.card c.supp) = S.card := by sorry

end ChvatalPolytopes.SeriesParallel
