-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H0_fibre_eq_one_of_subsingleton_H1_of_supportedIn_lineBundle
-- name    : AlgebraicGeometry.RelPicard.finrank_H0_fibre_eq_one_of_subsingleton_H1_of_supportedIn_lineBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f73b9f1c-0b06-5433-ab7a-0dae32ab9ccc
-- title:
--   h⁰=1 on a fibre from vanishing H¹ and Euler characteristic one
-- statement:
--   Let $R$ be a Noetherian commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper morphism of schemes, $U\subseteq C$ an open subscheme whose structure morphism $U\hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$, and $\varepsilon$ a morphism $\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ the identity. Let $\rho,e$ be natural numbers and let $E$, resp. $D_\gamma$, be a relative effective Cartier divisor on $C\times_R\operatorname{Spec}R$ of constant fibre rank $\rho$, resp. $e$, over the base (an ideal sheaf datum whose associated closed subscheme is finite, flat and locally of finite presentation over $\operatorname{Spec}R$), each with support contained in the preimage of $U$ under the first projection. Assume that for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every cover of the fibre over $x$ by two affine opens with affine intersection, the two-term Čech complex $\Gamma(U_0)\times\Gamma(U_1)\to\Gamma(U_0\cap U_1)$ of the restriction to that fibre of $E.\mathrm{lineBundle}\otimes D_\gamma.\mathrm{idealModule}$ (the dual of the ideal module of $E$ tensored with the ideal module of $D_\gamma$, i.e. $\mathcal O(E-D_\gamma)$) has $\dim_k\ker-\dim_k\operatorname{coker}=1$. Let $t\colon T\to\operatorname{Spec}R$ be a scheme over $\operatorname{Spec}R$ and $L$ a line bundle on $C\times_RT$ that is invertible and rigidified along the section determined by $\varepsilon$, and assume `FibrewiseAlgEquivZero L`: for every algebraically closed field and every point of $T$ with values in it, the restriction of $L$ to the corresponding fibre is algebraically equivalent to zero in the sense that it and the structure sheaf are the two specialisations, at two sections, of an invertible module over a geometrically integral parameter scheme of locally finite type. Finally let $k$ be a field, $s\colon\operatorname{Spec}k\to T$, and $\mathcal W$ a cover of the fibre $(C\times_RT)\times_Ts$ by two affine opens with affine intersection. If the cokernel of the Čech differential of $\mathcal W$ for the restriction to this fibre of $L\otimes(\mathcal O(E_T)\otimes\mathcal I(D_{\gamma,T}))$, where $E_T$ and $D_{\gamma,T}$ are the pullbacks of $E$ and $D_\gamma$ along $t$, is a subsingleton, then the kernel of that differential has $k$-dimension $1$.
--
--   This is the fibrewise $h^0=1$ statement for the twisted bundle $L\otimes\mathcal O(E-D_\gamma)$: vanishing of the Čech $H^1$ on a fibre together with Euler characteristic one on all geometric fibres pins the space of sections down to a line, the field $k$ being arbitrary rather than algebraically closed. It feeds the construction of a representable relative sub-Picard functor for families whose degenerate fibres are two smooth curves glued transversally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_finrank_H0_fibre_eq_one_of_subsingleton_H1_of_supportedIn_lineBundle.lean

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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.finrank_H0_fibre_eq_one_of_subsingleton_H1_of_supportedIn_lineBundle
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (ρ e : ℕ) (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover)
    (h1 : Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
      (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1 := by sorry
