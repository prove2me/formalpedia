-- Prove2me | Theorems.Thm_CombOpt_TJoin_char_vec_ineq_537
-- name    : CombOpt.TJoin.char_vec_ineq_537
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:52.810986+00:00
-- url     : https://prove2.me/theorems/adba6fa8-0f05-49ec-83e7-d93d9c3579f8
-- title:
--   The characteristic vector of a $T$-join satisfies the constraints of (5.37)
-- statement:
--   Let $G=(V,E)$ be a graph, $T\subseteq V$ with $|T|$ even, $J$ a $T$-join of $G$ and $x^*$ its characteristic vector. For every $S\subseteq V$ and every $F\subseteq\delta(S)$ such that $|F|+|S\cap T|$ is odd,
--
--   $$x^*(\delta(S)\setminus F)-x^*(F)\ge1-|F|.$$
--
--   Thus (5.37) is a relaxation of the optimal $T$-join problem for arbitrary costs, and its optimal value is a lower bound on the minimum cost of a $T$-join.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, p. 180 (PDF p. 188)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
import Definitions.Def_CombOpt_TJoin_charVec

namespace CombOpt.TJoin

open scoped symmDiff

/-- **T-joins satisfy the constraints of (5.37).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 180 (PDF p. 188): "Therefore, if F ⊆ δ(S) with |F| + |S ∩ T| odd, then
J ∩ δ(S) ≠ F. It follows that |J ∩ (δ(S)\F)| + |F\J| ≥ 1. Therefore, the characteristic vector
x* of J satisfies x*(δ(S)\F) − x*(F) ≥ 1 − |F|." -/
theorem char_vec_ineq_537 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (hT : Even T.card) (J : Finset E) (hJ : G.IsTJoin T J)
    (S : Finset V) (F : Finset E) (hF : F ⊆ G.cut S) (hodd : Odd (F.card + (S ∩ T).card)) :
    1 - (F.card : ℝ) ≤ ∑ e ∈ G.cut S \ F, charVec J e - ∑ e ∈ F, charVec J e := by sorry

end CombOpt.TJoin
