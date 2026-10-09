-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_ball_growth
-- name    : CycleLengthsExp.WellSpread.ball_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:54.157693+00:00
-- url     : https://prove2.me/theorems/4f7b009c-3ed8-452f-a0e8-3cec8c67bec9
-- title:
--   Proof of Lemma 2.1, p. 4 — in a (k,α)-expander, $|B_G(v,r)|\ge\min\{k,(1+\alpha)^r\}$
-- statement:
--   Let $k>0$ and $\alpha>0$ be reals and let $G$ be a finite $(k,\alpha)$-expander. Then for every vertex $v$ and every integer $r\ge 0$ the ball of radius $r$ around $v$ satisfies
--
--   $$|B_G(v,r)|\ \ge\ \min\{k,(1+\alpha)^r\}.$$
--
--   Balls grow geometrically until they reach size $k$. This is the fact behind the diameter bound of Lemma 2.1, and behind the logarithmic depth of the breadth-first trees in Lemma 2.7 and Theorem 1.
--
--   **Formalization Note.** $B_G(v,r)$ is the set of vertices reachable from $v$ by a walk with at most $r$ edges. The vertex type is any finite type.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 4, proof of Lemma 2.1, first sentence (cited there from Proposition 3.1 of [21])

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem ball_growth {V : Type*} [Fintype V] (G : SimpleGraph V) (k α : ℝ)
    (hk : 0 < k) (hα : 0 < α) (hG : IsKAlphaExpander k α G) (v : V) (r : ℕ) :
    min k ((1 + α) ^ r) ≤ ((ball G v r).ncard : ℝ) := by sorry

end CycleLengthsExp.WellSpread
