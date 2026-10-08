-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_NearOne_lemma_1b
-- name    : BlackwellDiscreteDP.NearOne.lemma_1b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:14.687992+00:00
-- url     : https://prove2.me/theorems/081db252-7ab4-4b4b-b76e-1e31e2cfc7c9
-- title:
--   Lemma 1(b) — rank(I − Q) + rank Q* = S
-- statement:
--   Let $Q$ be any $S\times S$ Markov matrix and $Q^*$ its Cesàro limit matrix. Then
--   $$\operatorname{rank}(I-Q)+\operatorname{rank}Q^*=S.$$
--
--   Equivalently, the dimension of the space of vectors fixed by $Q$ equals the rank of $Q^*$; this is the linear-algebraic fact behind the unique solvability in Lemma 1(c).
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 721, Lemma 1(b)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Lemma 1(b).** For any `S × S` Markov matrix `Q`, `rank (I − Q) + rank Q* = S`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 721, Lemma 1(b).

**Formalization Note.** `S = Fintype.card n`; ranks are `Matrix.rank` over `ℝ`. -/
theorem lemma_1b {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Q : Matrix n n ℝ) (hQ : IsMarkovMatrix Q) :
    (1 - Q).rank + (limitMatrix Q).rank = Fintype.card n := by sorry

end BlackwellDiscreteDP.NearOne
