-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery
-- name    : AlgebraicCurve.Divisor.exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/3f46c89b-ff64-5d78-a94f-97791e3dfc2e
-- title:
--   Divisor surgery: moving support into the good places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and work with the places of $F$ over $K$ in the project's sense: a `Place K F` is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. A divisor is a finitely supported function $D$ from these places to $\mathbb{Z}$; its degree is $\sum_V D(V)\cdot V.\mathrm{deg}$ for the integer invariant `Place.deg`, and $D$ is principal when there is a nonzero $f \in F$ with $D(V) = V.\mathrm{ord}\,f$ for every place $V$. Fix a predicate `good` on places. Assume the surgery hypothesis: for every place $V_0$ with $\neg\,\mathrm{good}\,V_0$ there is a principal divisor $p$ of degree $0$ with $p(V_0) = -1$ such that every place in the support of $p$ other than $V_0$ is good. Then for every divisor $D$ there exists a principal divisor $e$ of degree $0$ such that every place in the support of $D + e$ is good.
--
--   This is a moving (avoidance) lemma for divisors on a curve: any divisor class representative can be adjusted, within its linear equivalence class and keeping degree, so that its support avoids a prescribed set of bad places, given a one-place removal device at each bad place. It is used in the construction of specialisations of points on modular curves, where the bad places are those to be avoided when choosing a representative of a divisor class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (good : Place K F → Prop)
    (surgery : ∀ V₀ : Place K F, ¬ good V₀ →
      ∃ p : Divisor K F, Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
        ∀ V ∈ p.support, V ≠ V₀ → good V)
    (D : Divisor K F) :
    ∃ e : Divisor K F, Divisor.IsPrincipal e ∧ Divisor.degree e = 0 ∧
      ∀ V ∈ (D + e).support, good V := by sorry
