-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/cd5e44c8-0cde-5599-8e1a-8aa56c5ba761
-- title:
--   Two-chart Čech cohomology of mathcal O_X: h¹=g, h⁰=1
-- statement:
--   Let $K$ be an algebraically closed field and let $x\colon X\to\operatorname{Spec} K$ be a morphism of schemes with $X$ integral, $x$ proper and smooth of relative dimension $1$. Let $g$ be a natural number with the following property (`hg`): for every field $L$ that is a $K$-algebra, every `CurveModel K L` $M$ — that is, an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$, together with a ring isomorphism $L\simeq$ the function field of $M.C$ compatible with $K$, a bijection from the closed points of $M.C$ onto the places of $L/K$ (valuation subrings of $L$ containing the image of $K$, proper and with principal ideals) matching each stalk with the corresponding valuation subring, and the requirement that every finite set of points lies in some affine open — every isomorphism $e\colon M.C\cong X$ with $e$ followed by $x$ equal to $M.toBase$, every divisor $K_c$ (a finitely supported $\mathbb Z$-valued function on the places of $L/K$) and every natural number $g'$: if $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, where $\ell(D)$ is the $K$-dimension of the Riemann–Roch space of $D$ and $\deg$ is the degree weighted by residue degrees, then $g'=g$. Then for every pair $\mathcal V=(U_0,U_1)$ of affine opens of $X$ with $U_0\cup U_1=X$ and $U_0\cap U_1$ affine, the two-chart Čech data of the structure sheaf $\mathcal O_X$ (the unit object of $X$-modules), namely $\Gamma(U_0)$, $\Gamma(U_1)$, $\Gamma(U_0\cap U_1)$ with the two restrictions, regarded over $K$ via $x$, satisfies: the $K$-dimension of $H^1$, the quotient of $\Gamma(U_0\cap U_1)$ by the image of the Čech differential, equals $g$, and the $K$-dimension of $H^0$, the kernel of the Čech differential inside $\Gamma(U_0)\times\Gamma(U_1)$, equals $1$.
--
--   This is the classical computation $h^0(X,\mathcal O_X)=1$ and $h^1(X,\mathcal O_X)=g$ for a smooth proper integral curve over an algebraically closed field, stated in the two-chart Čech presentation of cohomology used throughout this development, with the genus pinned down by the Riemann–Roch formula satisfied by any curve model of $X$. It feeds the Euler-characteristic and relative Picard computations, and the identification of the genus with the dimension of the cotangent space of the zero section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (𝒱 : X.TwoAffineOpenCover) :
    Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 = g ∧
      Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 = 1 := by sorry
