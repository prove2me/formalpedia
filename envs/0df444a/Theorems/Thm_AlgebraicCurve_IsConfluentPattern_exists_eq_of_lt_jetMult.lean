-- Prove2me | Theorems.Thm_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult
-- name    : AlgebraicCurve.IsConfluentPattern.exists_eq_of_lt_jetMult
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/4e3341fe-c465-5723-a644-77d6c8ef5bac
-- title:
--   Orders in a confluent pattern exhaust {0,…,nᵥ-1}
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $M$ be a natural number, and let $P : \mathrm{Fin}\,M \to \mathrm{Place}\,K\,F$, $t : \mathrm{Fin}\,M \to F$ and $e : \mathrm{Fin}\,M \to \mathbb{N}$ be families indexed by $\{0,\dots,M-1\}$, where a `Place` of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and whose underlying ring is a principal ideal ring. Write $\mathrm{jetMult}\,P\,v$ for the number of indices $i$ with $P i = v$. Assume `IsConfluentPattern P t e`, that is: indices carrying the same place carry the same element of $F$ ($P i = P i'$ implies $t i = t i'$); the pair (place, order) determines the index ($P i = P i'$ and $e i = e i'$ imply $i = i'$); and for every $i$ one has $e i < \mathrm{jetMult}\,P\,(P i)$. Then for every index $i$ and every natural number $q < \mathrm{jetMult}\,P\,(P i)$ there exists an index $i'$ with $P i' = P i$ and $e i' = q$.
--
--   The statement says that in a confluent pattern the orders attached to the indices lying over a fixed place $v$ are exactly $0,1,\dots,n_v-1$, each occurring once, where $n_v$ is the number of such indices; the definition only demands injectivity and the bound, so surjectivity onto the initial segment is the extra information recorded here. It is used where rows of a jet (confluent evaluation) matrix belonging to one place are combined, namely in [`AlgebraicCurve.det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix`](thm.html#AlgebraicCurve.det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix) and [`ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix`](thm.html#ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.IsConfluentPattern.exists_eq_of_lt_jetMult
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} {P : Fin M → Place K F} {t : Fin M → F} {e : Fin M → ℕ}
    (hpat : IsConfluentPattern P t e) (i : Fin M) {q : ℕ} (hq : q < jetMult P (P i)) :
    ∃ i', P i' = P i ∧ e i' = q := by sorry
