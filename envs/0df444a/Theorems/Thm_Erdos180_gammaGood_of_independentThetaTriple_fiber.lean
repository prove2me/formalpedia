-- Prove2me | Theorems.Thm_Erdos180_gammaGood_of_independentThetaTriple_fiber
-- name    : Erdos180.gammaGood_of_independentThetaTriple_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:12:54.449138+00:00
-- url     : https://prove2.me/theorems/933639c4-aaa3-4091-aef7-72aeeab0a358
-- title:
--   Three common centres produce a copy of $S_3$
-- statement:
--   Let $G$ be bipartite with no $C_4$ and no $C_6$, let $T$ be an $R_S$-independent triple,
--   and let $v$ be a common centre of $T$. If $T$ has at least three common centres, then $v$ is a
--   centre of a copy of $S_3$, i.e. $v \notin U$.
--
--   This is Lemma 3.1(2) of the source in the case $k = 3$: if $r(T) \ge k$ then $B$ contains a copy
--   of $S_k$ with base set $T$, because the unique common neighbours of the $3k$ base-centre pairs
--   are distinct — a repetition would relate two bases or two centres. Contrapositively, if
--   $v \in U$ and $v \in L(T)$ then necessarily $r(T) = 2$, which is the step that lets $|U|$ be
--   estimated by the number of independent triples.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L5653-L5669

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Erdos180.gammaGood_of_independentThetaTriple_fiber
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) (vertex : V)
    (hvertex : vertex ∈ commonCenterFinset G triple.val)
    (hcard : 3 ≤ (commonCenterFinset G triple.val).card) :
    GammaGood G vertex := by sorry
