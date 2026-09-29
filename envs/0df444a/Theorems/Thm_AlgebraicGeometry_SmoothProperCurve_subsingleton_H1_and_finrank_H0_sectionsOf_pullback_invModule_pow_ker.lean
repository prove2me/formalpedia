-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
-- name    : AlgebraicGeometry.SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/81a06cf2-d891-5d9a-913f-141bef12de6e
-- title:
--   Fibrewise vanishing of H¹ and h⁰=m+1-g for 𝒪(mε)
-- statement:
--   Let $R$ be a commutative ring, $S=\operatorname{Spec}R$, and let $c\colon C\to S$ be proper, smooth of relative dimension one and geometrically integral. Let $\varepsilon$ be a pair consisting of a morphism $\varepsilon_1\colon S\to C$ together with the identity $\varepsilon_1\circ c=\mathrm{id}_S$ (read diagrammatically: $\varepsilon_1$ followed by $c$ is $\mathrm{id}_S$), i.e. a section of $c$. Let $g$ be a natural number subject to the following constancy hypothesis: for every algebraically closed field $k$, every morphism $s\colon\operatorname{Spec}k\to S$, every field $L$ over $k$, every `CurveModel` $M$ for $L/k$ (a scheme $M.C$, proper and smooth of relative dimension one over $k$, integral, with function field identified with $L$ compatibly with $k$, whose closed points correspond bijectively to the places of $L/k$ with matching valuation subrings, and in which every finite set of points lies in one affine open) together with an isomorphism $e\colon M.C\cong C\times_S\operatorname{Spec}k$ over $k$, every divisor $K_c$ of $L/K$ and every $g'$: if $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, where $\ell(D)$ is the $k$-dimension of the Riemann–Roch space of $D$, then $g'=g$. Let $m$ be a natural number with $2g\le m+1$, let $\mathcal V$ be a cover of $C$ by two affine opens $U_0,U_1$ with $U_0\sqcup U_1=C$ and $U_0\cap U_1$ affine, and let $K$ be a field which is an $R$-algebra. Form the base change $C_K=C\times_S\operatorname{Spec}K$, the pulled-back two-chart cover $\mathcal V_K$, and the module $\mathrm{pr}_1^{*}\bigl((\ker\varepsilon_1)^{m}\bigr)^{\vee}$ on $C_K$, where $(\ker\varepsilon_1)^{m}$ is the $m$-th power of the ideal sheaf data of $\varepsilon_1$ and $(-)^{\vee}$ is the dual module. Then the two-chart Čech complex of this module for $\mathcal V_K$ over $K$, with $H^1$ the quotient of the sections over $U_0\cap U_1$ by the image of the Čech difference and $H^0$ its kernel inside the product of the sections over $U_0$ and over $U_1$, satisfies: $H^1$ is a subsingleton, and $\dim_K H^0=m+1-g$ (truncated subtraction of natural numbers).
--
--   This is the fibrewise Riemann–Roch input for the sheaf $\mathcal O(m\varepsilon)=(\mathcal I_\varepsilon^{m})^{\vee}$ on a pointed smooth proper curve of constant genus $g$ with $m\ge 2g-1$: the first Čech cohomology of every fibre vanishes and the zeroth has constant dimension $m+1-g$. It is used in the construction of sections of $\mathcal O(m\varepsilon)$ avoiding prescribed points and in the surjectivity of the unit map on global sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (m : ℕ) (hm : 2 * g ≤ m + 1) (𝒱 : C.TwoAffineOpenCover)
    (K : Type u) [Field K] [Algebra R K] :
    Subsingleton ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj
          ((ε.1.ker ^ m).invModule))).H1 ∧
      Module.finrank K ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj
          ((ε.1.ker ^ m).invModule))).H0 = m + 1 - g := by sorry
