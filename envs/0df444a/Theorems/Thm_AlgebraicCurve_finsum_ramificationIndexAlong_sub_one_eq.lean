-- Prove2me | Theorems.Thm_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq
-- name    : AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/95bdc102-f811-5e21-a50f-5a9cfc9cf2dc
-- title:
--   Riemann–Hurwitz formula for the cover F/K(f)
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and let $F$ be a field, given as a $K$-algebra, which is a curve over $K$ in the sense of `IsCurveOver`: every nonzero $h \in F$ admits a finitely supported $\mathbb{Z}$-valued divisor on the places of $F/K$ whose value at each place $v$ is $v.\mathrm{ord}(h)$ and whose degree is $0$; each place has residue field finite over $K$; and $\Omega[F/K]$ is free of rank $1$ over $F$. Assume in addition that $F$ is essentially of finite type over $K$ and that `HasCanonicalDivisor` holds, i.e. for every nonzero $\omega \in \Omega[F/K]$ the function $v \mapsto v.\mathrm{ord}(v.\mathrm{differentialCoeff}\,\omega)$ is the value function of a finitely supported divisor. Here a place is a valuation subring of $F$, distinct from $F$, containing the image of $K$ and a principal ideal ring. Let $f \in F$ be transcendental over $K$ and suppose $F$ is finite-dimensional over the intermediate field $K(f) =$ `adjoin K {f}`. Then the sum, over all places $w$ of $F/K$, of $e_w - 1$, where $e_w$ is the ramification index of $w$ along the inclusion $K(f) \hookrightarrow F$ — the least $n > 0$ for which some nonzero $g \in K(f)$ has $w.\mathrm{ord}(g) = n$ — equals $$2\,\dim_K \mathrm{regularDifferentials}(K,F) - 2 + 2\,[F : K(f)],$$ the regular differentials being those $\omega \in \Omega[F/K]$ such that at each place $v$ one may write $\omega = h \cdot d(\pi_v)$ with $h$ in the valuation ring of $v$ and $\pi_v$ a uniformiser at $v$.
--
--   This is the Riemann–Hurwitz (Hurwitz genus) formula in the tame, characteristic-zero setting, for the covering of the projective line determined by a transcendental element $f$, with the genus of $F$ appearing as the dimension of the space of regular differentials. It is used in the computation of the total ramification of such a map, notably by [`AlgebraicCurve.Place.sum_ramification_evalAt_eq`](thm.html#AlgebraicCurve.Place.sum_ramification_evalAt_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {f : F} (htr : Transcendental K f)
    [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] :
    (∑ᶠ w : Place K F, ((Place.ramificationIndexAlong (adjoin K ({f} : Set F)).val w : ℤ) - 1)) =
      2 * (Module.finrank K ↥(regularDifferentials K F) : ℤ) - 2 +
      2 * (Module.finrank (↥(adjoin K ({f} : Set F))) F : ℤ) := by sorry
