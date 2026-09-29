-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn
-- name    : AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d22233f9-c010-5448-b37d-32366d5d8372
-- title:
--   Euler characteristic one for 𝒪(rε)⊗ I_D on a fibre
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec} R$ a proper morphism; let $U\subseteq C$ be an open subscheme such that the composite of the inclusion $U\hookrightarrow C$ with $c$ is smooth of relative dimension $1$; let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R\to C$ whose composite with $c$ is the identity) whose set-theoretic image lies in $U$. Let $g,e,r$ be natural numbers with $g+e=r$, and let $D$ be a relative effective Cartier divisor of degree $e$ for $c$ over the identity of $\operatorname{Spec} R$: an ideal sheaf datum $D.I$ on $C\times_{\operatorname{Spec} R}\operatorname{Spec} R$ whose associated closed subscheme is finite, flat and locally of finite presentation over the base with fibre rank $e$ at every point; assume $D$ is supported in $U$, i.e. the support of $D.I$ is contained in the preimage of $U$ under the first projection. Let $k$ be a field and $x\colon\operatorname{Spec} k\to\operatorname{Spec} R$ a point, and write $X$ for the fibre $\bigl(C\times_{\operatorname{Spec} R}\operatorname{Spec} R\bigr)\times_{\operatorname{Spec} R}\operatorname{Spec} k$, viewed over $\operatorname{Spec} k$ by the second projection `fibreAt`. Assume that for every two-chart affine open cover $\mathcal{W}$ of $X$ (two affine opens $U_0,U_1$ with $U_0\sqcup U_1$ covering $X$ and $U_0\cap U_1$ affine) the two-chart Čech complex of the structure sheaf — the unit object of sheaves of modules on $X$ — has $\dim_k H^0=1$ and $\dim_k H^1=g$, where $H^0$ is the kernel and $H^1$ the cokernel of the Čech difference map. Then for every such cover $\mathcal{W}$, the module $\bigl(\mathcal{I}_\varepsilon^{\,r}\bigr)^{\vee}\otimes D.I$, i.e. the tensor product of the dual of the module of the $r$-th power of the ideal of the section $\varepsilon$ with the ideal module of $D$, pulled back to the fibre $X$, satisfies $$\dim_k H^0-\dim_k H^1=1$$ for its two-chart Čech complex on $\mathcal{W}$.
--
--   This is the Riemann–Roch count $\chi\bigl(\mathcal{O}(r\varepsilon-D)\bigr)=1-g+(r-e)=1$ on a geometric fibre, computed throughout in terms of the two-chart Čech complex and requiring only the invertibility of the ideals of $r\varepsilon$ and of $D$, which holds because their supports lie in the relatively smooth open $U$; the fibre itself may be singular. It supplies the per-fibre Euler-characteristic input to [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r)
    (D : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDU : D.SupportedIn U)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

    (hH0 : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k ↥(𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = 1)
    (hg : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    (Module.finrank k ↥(𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ D.idealModule))).H0 : ℤ) -
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ D.idealModule))).H1 = 1 := by sorry
