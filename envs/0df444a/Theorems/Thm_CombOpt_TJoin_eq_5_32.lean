-- Prove2me | Theorems.Thm_CombOpt_TJoin_eq_5_32
-- name    : CombOpt.TJoin.eq_5_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:58.148989+00:00
-- url     : https://prove2.me/theorems/c6bb7f09-627e-4c12-9250-142c966879c2
-- title:
--   (5.32) — a $T$-join meets every $T$-cut: $x(\delta(S))\ge1$
-- statement:
--   Let $G=(V,E)$ be a graph, $T\subseteq V$ with $|T|$ even, $J$ a $T$-join of $G$ and $x$ its characteristic vector. For every $T$-odd set $S\subseteq V$ (that is, $|S\cap T|$ odd),
--
--   $$x(\delta(S))\ge1. \tag{5.32}$$
--
--   Hence the linear program (5.33) is a lower bound for the cost of any $T$-join.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, (5.32), p. 178 (PDF p. 186)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_charVec

namespace CombOpt.TJoin

open scoped symmDiff

/-- **The T-cut inequality (5.32).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, (5.32), p. 178 (PDF p. 186): "A set S ⊆ V is T-odd if |S ∩ T| is odd. In this case
δ(S) is called a T-cut. … the characteristic vector x of any T-join of G satisfies
x(δ(S)) ≥ 1. (5.32)" -/
theorem eq_5_32 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (J : Finset E) (hJ : G.IsTJoin T J)
    (S : Finset V) (hS : Odd (S ∩ T).card) :
    1 ≤ ∑ e ∈ G.cut S, charVec J e := by sorry

end CombOpt.TJoin
