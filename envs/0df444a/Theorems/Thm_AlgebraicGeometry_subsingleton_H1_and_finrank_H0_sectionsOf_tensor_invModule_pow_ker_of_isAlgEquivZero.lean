-- Prove2me | Theorems.Thm_AlgebraicGeometry_subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
-- name    : AlgebraicGeometry.subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/0e57e68e-acac-57d2-b539-1624c0876d89
-- title:
--   Vanishing of H¹ and h⁰=r+1-g for L(rp)
-- statement:
--   Let $K$ be an algebraically closed field and $x : X \to \operatorname{Spec} K$ a morphism of schemes with $X$ integral, $x$ proper and smooth of relative dimension $1$. Let $g$ be a natural number subject to the hypothesis `hg`, which says that $g$ is the Riemann–Roch genus of $X$: for every field extension $L$ of $K$, every `CurveModel K L` (an integral scheme $M.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$, together with a ring isomorphism $L \cong$ the function field of $M.C$ compatible with $K$, a bijection from the closed points of $M.C$ to the places of $L/K$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open), every isomorphism $e : M.C \cong X$ with $e$ followed by $x$ equal to the structure morphism of the model, every divisor $K_c$ (a finitely supported $\mathbb Z$-valued function on places) and every $g'$, if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$, then $g' = g$. Let $p : \operatorname{Spec} K \to X$ be a section of $x$, i.e. $p$ followed by $x$ is the identity. Let $L$ be a module on $X$ which is invertible (every point has an open neighbourhood on which the restriction is isomorphic to the unit module) and satisfies `IsAlgEquivZero x L`: there are a scheme $T'$ with a locally of finite type, geometrically integral morphism $h : T' \to \operatorname{Spec} K$, an invertible module $M$ on $X \times_{\operatorname{Spec} K} T'$ and two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} K$ such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module, while the pullback along the base change of $t_1$ is isomorphic to the pullback of $L$. Let $r$ be a natural number with $2g \le r+1$, and let $\mathcal V$ be a cover of $X$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine. Then, for the two-chart Čech complex of $L \otimes (p_{\ast}\text{-kernel ideal sheaf})^{r}$-dual, that is of $L \otimes ((p.\mathrm{ker})^r).\mathrm{invModule}$ (the dual of the module of the $r$-th power of the ideal sheaf of the section $p$), the group $H^1 = \Gamma(U_0 \cap U_1)$ modulo the image of the Čech difference is a subsingleton, and $H^0$, the kernel of the Čech difference in $\Gamma(U_0) \times \Gamma(U_1)$, has $K$-dimension $r + 1 - g$ (truncated subtraction in $\mathbb N$, harmless since $g \le r+1$).
--
--   This is Riemann–Roch together with the vanishing theorem in the shape needed for line bundles of the form $L(rp)$ with $L$ algebraically equivalent to zero and $r \ge 2g-1$, computed by Čech cohomology on a two-chart affine cover. It is the curve-theoretic input for the construction of Picard bundles and is cited in the statements about families of invertible modules algebraically equivalent to zero and about the Poincaré bundle twisted by a section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicCurve

theorem AlgebraicGeometry.subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (r : ℕ) (hr : 2 * g ≤ r + 1) (𝒱 : X.TwoAffineOpenCover) :
    Subsingleton (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H1 ∧
      Module.finrank K (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H0 = r + 1 - g := by sorry
