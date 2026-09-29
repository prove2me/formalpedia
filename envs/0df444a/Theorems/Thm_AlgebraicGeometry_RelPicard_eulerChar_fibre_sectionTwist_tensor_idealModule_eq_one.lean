-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
-- name    : AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/5233e0a8-b399-5af6-898a-5f1052a9395f
-- title:
--   Euler characteristic one for 𝒪(rε)⊗𝒪(-D) on geometric fibres
-- statement:
--   Let $R$ be a commutative ring and let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, with $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity). Let $g, e, r$ be natural numbers with $g + e = r$, and let $D_\gamma$ be a relative effective Cartier divisor of degree $e$ for $c$ over the identity of $\operatorname{Spec} R$: an ideal sheaf datum $I$ on $C \times_{\operatorname{Spec} R} \operatorname{Spec} R$ whose closed subscheme inclusion, followed by the second projection, is finite, flat and locally of finite presentation with fibre rank $e$ at every point. Assume the genus hypothesis: for every algebraically closed field $k$, every morphism $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$, every field $L$ over $k$, every curve model $M$ of $L/k$ and every isomorphism $M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ carrying the second projection to the structure morphism of $M$, and every divisor $K_c$ on $L/k$ and natural number $g'$ such that $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ (with $\ell$ the $k$-dimension of the Riemann–Roch space), one has $g' = g$. Then for every algebraically closed field $k$, every $x \colon \operatorname{Spec} k \to \operatorname{Spec} R$ and every cover $\mathcal{W}$ of the fibre $(C \times_{\operatorname{Spec} R} \operatorname{Spec} R) \times_{\operatorname{Spec} R} \operatorname{Spec} k$ by two affine opens with affine intersection and union everything, the two-chart Čech Euler characteristic of the pullback to that fibre of $(\mathcal{I}_\varepsilon^{\,r})^{\vee} \otimes I_{D_\gamma}$ is one: the $k$-dimension of the kernel of the Čech differential $\Gamma(U_0) \times \Gamma(U_1) \to \Gamma(U_0 \cap U_1)$ minus the $k$-dimension of its cokernel equals $1$.
--
--   This is the Euler-characteristic normalisation $\chi(\mathcal{O}(r\varepsilon)\otimes\mathcal{O}(-D)) = 1$ on geometric fibres, in the degree range $\deg D = r - g$, for a relative curve of constant genus $g$ with a section; it is the form in which Riemann–Roch enters the construction of affine charts on the relative Picard scheme. It is used in [`AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced`](thm.html#AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1 := by sorry
