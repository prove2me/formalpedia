-- Prove2me | Theorems.Thm_ChinesePostman_Mixed_cut_balance_of_symmetric
-- name    : ChinesePostman.Mixed.cut_balance_of_symmetric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:45.713368+00:00
-- url     : https://prove2.me/theorems/6db81a4e-db32-494d-9177-14fe6c1f2eae
-- title:
--   §6, p. 116 — in a symmetric mixed graph every node set has as many directed edges leaving it as entering it
-- statement:
--   Let $G$ be a mixed graph that is **symmetric**: every node $n$ has as many directed edges directed away from $n$ as directed toward $n$. Then for every set $S$ of nodes,
--
--   $$
--   \#\{e \text{ directed} : \operatorname{tail}(e) \in S,\ \operatorname{head}(e) \notin S\} \;=\; \#\{e \text{ directed} : \operatorname{head}(e) \in S,\ \operatorname{tail}(e) \notin S\},
--   $$
--
--   that is, $S$ has the same number of edges directed away from a node of $S$ and toward a node not in $S$ as edges directed toward a node of $S$ and away from a node not in $S$.
--
--   This is the reason, in the paper, that every arborescence of directed edges can be extended to a spanning one.
--
--   **Formalization Note** Only directed edges are counted; undirected edges play no role. The paper states the fact for a symmetric, connected graph whose edges are all directed; connectivity is not used and is not assumed.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 116, §6 (the reason a maximal arborescence is spanning)

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, p. 116: in a symmetric mixed graph every node set `S` has as many directed edges
directed away from a node of `S` and toward a node not in `S` as directed edges directed toward
a node of `S` and away from a node not in `S`. -/
theorem cut_balance_of_symmetric {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (S : Finset V) :
    (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e ∈ S ∧ G.head e ∉ S)).card =
      (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e ∈ S ∧ G.tail e ∉ S)).card := by sorry

end ChinesePostman.Mixed
