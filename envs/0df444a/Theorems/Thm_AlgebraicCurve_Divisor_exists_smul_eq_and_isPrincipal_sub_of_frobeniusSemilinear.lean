-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear
-- name    : AlgebraicCurve.Divisor.exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/dfb820ff-f247-5262-b16d-346c55dafaaa
-- title:
--   Frobenius-fixed divisor classes contain Frobenius-fixed divisors
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, and assume the two global hypotheses on $F/K$: [`AlgebraicCurve.HasPrincipalDivisors K F`](def/AlgebraicCurve_DivisorClassGroup.html#L217), i.e. every $f \in F^{\times}$ has a finitely supported divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ of $F/K$ and $\deg D = 0$; and [`AlgebraicCurve.ConstantsAreBase K F`](def/AlgebraicCurve_AdelicIndex.html#L45), i.e. the Riemann–Roch space $\mathcal L(0)$ of the zero divisor equals the image of $K$ in $F$. Here a place is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring, and a divisor is a finitely supported $\mathbb Z$-valued function on the places. Let $q$ be a natural number and let $\beta$ be a semilinear automorphism of $F/K$, that is, a pair consisting of a ring automorphism of $F$ and one of $K$ compatible with the structure map, such that the automorphism induced on $K$ is $a \mapsto a^{q}$, and such that every $x \in F$ is fixed by some positive power of $\beta$. Let $D$ be a divisor whose class is fixed by $\beta$, in the sense that $\beta \cdot D - D$ is principal: it is the divisor of orders of some nonzero element of $F$. Then there exists a divisor $D'$ with $\beta \cdot D' = D'$ and $D - D'$ principal.
--
--   This is the descent statement of F. K. Schmidt for the constant-field Frobenius: in the setting $K = \overline{\mathbb F}_q$, $F = \overline{\mathbb F}_q F_0$ with $\beta$ the arithmetic Frobenius, every Frobenius-stable divisor class is represented by a Frobenius-stable divisor. It is used in the identification of the Frobenius fixed points on $\mathrm{Pic}^0$ of the geometric function field with $\mathrm{Pic}^0$ over the finite field, via [`AlgebraicCurve.Pic0.natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius`](thm.html#AlgebraicCurve.Pic0.natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.exists_smul_eq_and_isPrincipal_sub_of_frobeniusSemilinear
    (K F : Type*) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] (hKF : AlgebraicCurve.ConstantsAreBase K F)
    (q : ℕ) (β : AlgebraicCurve.SemilinearAut K F)
    (hβK : ∀ a : K, AlgebraicCurve.SemilinearAut.baseAut β a = a ^ q)
    (hβF : ∀ x : F, ∃ n : ℕ, 0 < n ∧ β ^ n • x = x)
    (D : AlgebraicCurve.Divisor K F) (hD : (β • D - D).IsPrincipal) :
    ∃ D' : AlgebraicCurve.Divisor K F, β • D' = D' ∧ (D - D').IsPrincipal := by sorry
