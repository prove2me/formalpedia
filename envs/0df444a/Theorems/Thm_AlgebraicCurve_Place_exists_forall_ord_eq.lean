-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
-- name    : AlgebraicCurve.Place.exists_forall_ord_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/8207ed75-3836-512d-b38f-8500b0fad483
-- title:
--   Prescribed orders at finitely many places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. A place of $F$ over $K$, in the sense of the structure `Place`, consists of a valuation subring $\mathcal{O}_v \subseteq F$ that contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring; attached to such a $v$ there is the adic valuation [`AlgebraicCurve.Place.adicValuation`](def/AlgebraicCurve_DivisorClassGroup.html#L102), the $\mathbb{Z}^{m0}$-valued valuation of $F$ associated with the height-one prime of $\mathcal{O}_v$, and the order function $\operatorname{ord}_v(f) = -\log(v.\mathrm{adicValuation}\, f)$, an integer-valued function on $F$. The assertion is that for every finite set $T$ of places of $F$ over $K$ and every assignment $n$ of an integer to each place (only the values of $n$ on $T$ play a role), there exists an element $f \in F$ with $f \neq 0$ and $\operatorname{ord}_v(f) = n(v)$ for all $v \in T$. No further hypotheses on $K$, $F$ or $T$ are imposed; in particular $T$ may be empty.
--
--   This is the weak approximation (Artin–Whaples) theorem in the form that finitely many independent orders of vanishing can be prescribed simultaneously by a single nonzero function. It is used throughout the divisor theory of the project, for instance in the comparison of divisor degrees with dimensions of spaces of functions and in the computation of pushforwards and pullbacks of divisors along field extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_forall_ord_eq.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_forall_ord_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (Place K F)) (n : Place K F → ℤ) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ T, v.ord f = n v := by sorry
