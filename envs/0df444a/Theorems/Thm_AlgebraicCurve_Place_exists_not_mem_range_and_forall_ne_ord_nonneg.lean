-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_not_mem_range_and_forall_ne_ord_nonneg
-- name    : AlgebraicCurve.Place.exists_not_mem_range_and_forall_ne_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/bec03f94-6b56-5e39-bf55-2171a70af6df
-- title:
--   A non-constant function with poles only at a prescribed place
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`; the latter asserts three things: every nonzero $f \in F$ has a divisor $D$ of degree $0$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$, the residue field of every place is a finite-dimensional $K$-vector space, and the module of Kähler differentials $\Omega[F/K]$ is free of rank $1$ over $F$. Here a place of $F$ over $K$ is a valuation subring of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; and $\operatorname{ord}_v(f)$ is minus the logarithm of the value of $f$ under the valuation attached to the height-one prime of that valuation subring. Let $P$ be such a place. The assertion is that there exists $y \in F$ which does not lie in the image of $K \to F$ and satisfies $\operatorname{ord}_Q(y) \ge 0$ for every place $Q \ne P$; that is, a non-constant element of $F$ whose poles, if any, are concentrated at $P$.
--
--   This is the standard consequence of the Riemann inequality that for each place $P$ of a function field in one variable over an algebraically closed field the Riemann–Roch space $L(N \cdot P)$ contains non-constant functions for $N$ large. It is used in the construction of regular prolongations and residue discs, and in the proof that the point-to-place map of a Mumford-type quotient is surjective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_not_mem_range_and_forall_ne_ord_nonneg.lean

import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_not_mem_range_and_forall_ne_ord_nonneg
    (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] (P : Place K F) :
    ∃ y : F, y ∉ Set.range (algebraMap K F) ∧ ∀ Q : Place K F, Q ≠ P → 0 ≤ Q.ord y := by sorry
