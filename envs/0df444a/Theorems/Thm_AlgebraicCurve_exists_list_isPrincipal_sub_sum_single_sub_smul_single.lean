-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single
-- name    : AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/d394eeb7-4d00-568a-8d0e-6a0492a164d6
-- title:
--   Degree-zero divisors are equivalent to sumᵢ [vᵢ] - r[v₀]
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`, i.e. every nonzero element of $F$ has a divisor of degree $0$ (`HasPrincipalDivisors`), every place of $F/K$ has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank $1$ over $F$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on the set of places, its degree being $\sum_v D(v)\deg v$. Fix a place $v_0$ and a divisor $D$ with $\deg D = 0$. The assertion is that there exists a finite list $l = (v_1,\dots,v_r)$ of places, repetitions allowed, with $r$ its length, such that the divisor $$D - \Bigl(\sum_{i=1}^{r}[v_i] - r\,[v_0]\Bigr)$$ is principal, that is, there is some $f \in F$, $f \neq 0$, whose order at every place $v$ equals the value of this divisor at $v$.
--
--   This is the standard consequence of the Riemann–Roch theorem that on a curve over an algebraically closed field every degree-zero divisor class is represented by $\sum_i (P_i - P_0)$ for a suitable finite family of points, packaged with the family presented as a list so that the class can be matched with a tensor product $\bigotimes_i \mathcal{O}(P_i - P_0)$ of line bundles. It is used in the description of the degree-zero Picard group of a curve by its points and in the Abel–Jacobi dictionary for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (v₀ : Place K F) (D : Divisor K F) (hD : Divisor.degree D = 0) :
    ∃ l : List (Place K F),
      Divisor.IsPrincipal
        (D - ((l.map fun v => Finsupp.single v (1 : ℤ)).sum - (l.length : ℤ) • Finsupp.single v₀ 1)) := by sorry
