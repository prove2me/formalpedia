-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
-- name    : AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f8ef513e-ac17-5d72-b895-aeb32008b43b
-- title:
--   Fibre cohomology of a rigidified bundle twisted by rε
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper morphism, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity). Let $g$ be a natural number satisfying the following genus hypothesis `hg`: for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$, every field $L$ over $k$, every `CurveModel k L` $M$ (a scheme integral, proper and smooth of relative dimension one over $\operatorname{Spec}k$, together with an identification of $L$ with its function field over $k$, a bijection between its closed points and the places of $L/k$ matching stalks with valuation subrings, and the property that finite sets lie in affine opens) together with an isomorphism $e\colon M.C\cong C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ over $\operatorname{Spec}k$, every divisor $K_c$ on $L/k$ and every $g'$: if $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, where $\ell$ is the $k$-dimension of the Riemann–Roch space, then $g'=g$. Let $t\colon T\to\operatorname{Spec}R$ be a scheme over $R$ and $M$ a rigidified line bundle on $C\times_{R}T$, that is, an invertible module $M.L$ whose pullback along the section `rigSection c t ε` is trivial. Assume `FibrewiseAlgEquivZero M`: for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$, the pullback of $M.L$ to the fibre satisfies `IsAlgEquivZero` over the structure morphism `fibreAt c t s`, i.e. there are a scheme $T'$ locally of finite type and geometrically integral over $\operatorname{Spec}k$, an invertible module on the base change of the fibre to $T'$, and two sections of $T'$ along which that module pulls back to the unit module and to the pullback of $M.L$ respectively. Let $r$ be a natural number with $2g\le r+1$. Then for every algebraically closed field $k$, every $s\colon\operatorname{Spec}k\to T$, and every cover $\mathcal W$ of the fibre $(C\times_RT)\times_T\operatorname{Spec}k$ by two affine opens with affine intersection whose union is everything, the two-term Čech complex of $k$-modules of sections of the restriction to the fibre of $M.L\otimes(\mathcal I_\varepsilon^{\,r})^{\vee}$, where $\mathcal I_\varepsilon$ is the kernel ideal sheaf of `rigSection c t ε`, has $H^1$ (the quotient of the sections on the intersection by the image of the difference map) a subsingleton, and its $H^0$ (the kernel of that map) has $k$-dimension $r+1-g$, the subtraction being in $\mathbb N$.
--
--   This is the Riemann–Roch input for Picard bundles: a rigidified line bundle that is fibrewise algebraically equivalent to zero has degree zero on each geometric fibre, so its twist by $r$ times the section has degree $r>2g-2$ and thus vanishing $H^1$ and $h^0=r+1-g$. It is the algebraically closed residue field case, used by [`AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero`](thm.html#AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero) and by [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicCurve
open AlgebraicGeometry

theorem AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 =
          r + 1 - g := by sorry
