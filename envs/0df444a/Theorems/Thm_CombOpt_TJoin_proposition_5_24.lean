-- Prove2me | Theorems.Thm_CombOpt_TJoin_proposition_5_24
-- name    : CombOpt.TJoin.proposition_5_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:47.356+00:00
-- url     : https://prove2.me/theorems/f1ca178b-7b84-4b3a-baaf-61cce9b57881
-- title:
--   Proposition 5.24 — $J$ is a $T$-join iff $J\triangle J'$ is a $(T\triangle T')$-join
-- statement:
--   Let $G=(V,E)$ be a graph, let $T,T'\subseteq V$ with $|T|$ and $|T'|$ even, and let $J'$ be a $T'$-join of $G$. Then for every $J\subseteq E$,
--
--   $$J \text{ is a } T\text{-join of } G \iff J\triangle J' \text{ is a } (T\triangle T')\text{-join of } G.$$
--
--   This observation lets one pass between join problems with different terminal sets, and is used to turn arbitrary costs into nonnegative ones.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 5.24, p. 168 (PDF p. 176)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin

namespace CombOpt.TJoin

open scoped symmDiff

/-- **Proposition 5.24 (symmetric differences of joins).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 5.24, p. 168 (PDF p. 176): "Let J′ be a T′-join of G. Then J is a T-join of G
if and only if J △ J′ is a (T △ T′)-join of G."

`|T|` and `|T′|` are even: the book defines T-joins under that standing assumption (p. 167). -/
theorem proposition_5_24 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T T' : Finset V) (hT : Even T.card) (hT' : Even T'.card)
    (J J' : Finset E) (hJ' : G.IsTJoin T' J') :
    G.IsTJoin T J ↔ G.IsTJoin (T ∆ T') (J ∆ J') := by sorry

end CombOpt.TJoin
