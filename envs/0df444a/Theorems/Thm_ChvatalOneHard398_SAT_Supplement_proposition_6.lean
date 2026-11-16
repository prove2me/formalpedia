-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_proposition_6
-- name    : ChvatalOneHard398.SAT.Supplement.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:30.416033+00:00
-- url     : https://prove2.me/theorems/7d76a130-ac0b-4203-8a0c-04677635b758
-- title:
--   Proposition 6 — thin subpolyhedra
-- statement:
--   Let $Q=Q(B,t,r)$ have rational nonsingular $B$, rational $t$ and rational radius satisfying
--   $$0<r<\frac{\lambda_1(B\mathbb Z^d)}{2d^2}.$$
--   Every rational subpolyhedron of $Q$ has Chvátal rank at most one, and $Q$ contains at most one integral vector.
--
--   This hereditary statement supplies the oracle promise for Theorem 7 and the rank consequence of Theorem 12.
--
--   Differences from the source:
--   - encoding: Euclidean vectors and column lattice bases → Fin d coordinates and column-generated EuclideanSpace lattices; reason: the finite coordinates and Euclidean norm represent the same vectors and bases
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.11, Proposition 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem proposition_6 (Q : ParaInput) (hQ : Q.Thin) :
    hereditaryRankOne Q.poly ∧ Subsingleton (integralPoints Q.poly) := by sorry

end ChvatalOneHard398.SAT.Supplement
