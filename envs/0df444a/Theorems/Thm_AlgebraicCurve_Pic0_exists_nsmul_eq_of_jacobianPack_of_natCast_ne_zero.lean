-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
-- name    : AlgebraicCurve.Pic0.exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/6fcecda7-ed5a-5735-912b-21fd02c304c9
-- title:
--   Divisibility of Pic⁰ by n invertible in K
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ which is finitely generated of transcendence degree one in the sense that some $x \in F$ is transcendental over $K$ and $F$ is finite-dimensional over the intermediate field $K(x)$, and assume `IsCurveOver K F`: every nonzero $f \in F$ has a principal divisor, i.e. a finitely supported function $D$ on the places of $F$ over $K$ (valuation subrings of $F$ containing $K$, proper and principal) with $D(v) = \mathrm{ord}_v(f)$ for all $v$ and $\deg D = 0$; each residue field $v$ is finite over $K$; and $\Omega_{F/K}$ is free of rank one over $F$. Let $J$ be a scheme with a morphism $c : J \to \operatorname{Spec} K$ that is smooth and proper, with $J$ connected, let $\mathrm{mul}$ be a morphism from the pullback of $c$ along itself to $J$, and let $\mathrm{pts}$ be a bijection from $\mathrm{Pic}^0(K,F)$ — degree-zero divisors modulo principal divisors — onto the sections of $c$, such that for all $x, y$ the section attached to $x + y$ is the morphism to the pullback determined by the sections of $x$ and $y$, followed by $\mathrm{mul}$. Then for every natural number $n \neq 0$ with $n \neq 0$ in $K$ and every $x \in \mathrm{Pic}^0(K,F)$ there is $y$ with $n \cdot y = x$. No group-scheme axioms are imposed on $\mathrm{mul}$ beyond its computing the addition of $\mathrm{Pic}^0$ on $K$-points through $\mathrm{pts}$.
--
--   This is the divisibility of the group of $K$-points of the Jacobian by an integer $n$ invertible in $K$, obtained in the classical way from the fact that multiplication by such an $n$ is étale, together with the surjectivity of an étale morphism that is proper onto a connected target; here the Jacobian enters only through a smooth proper connected scheme over $K$ whose $K$-points carry the group $\mathrm{Pic}^0$. It is used, via [`AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self`](thm.html#AlgebraicCurve.Pic0.exists_zsmul_eq_of_finiteDimensional_ratFunc_of_forall_pow_eq_self), to establish divisibility properties of divisor class groups of curves over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve CategoryTheory

theorem AlgebraicCurve.Pic0.exists_nsmul_eq_of_jacobianPack_of_natCast_ne_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (J : AlgebraicGeometry.Scheme)
    (c : J ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hsm : AlgebraicGeometry.Smooth c)
    (hpr : AlgebraicGeometry.IsProper c)
    (hconn : ConnectedSpace J)
    (mul : CategoryTheory.Limits.pullback c c ⟶ J)
    (pts : Pic0 K F ≃
      {σ : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ J // σ ≫ c = 𝟙 _})
    (hadd : ∀ x y : Pic0 K F, (pts (x + y)).1 =
      CategoryTheory.Limits.pullback.lift (pts x).1 (pts y).1
        ((pts x).2.trans (pts y).2.symm) ≫ mul)
    (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) (x : Pic0 K F) :
    ∃ y : Pic0 K F, n • y = x := by sorry
