-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
-- name    : AlgebraicGeometry.RelPicard.exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/46a979c9-a019-5785-a459-3c817ccd054e
-- title:
--   An open chart of relative Pic⁰ from one divisor
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Assume, first, that for every $m_0$ there is finite map data `SmoothProperCurve.FiniteMapData` for $(c,\varepsilon)$ with degree parameter $m \ge m_0$; second, natural numbers $g, e, r$ with $g + e = r$ and a relative effective Cartier divisor $D_\gamma$ of degree $e$ on $C$ over the identity of $\operatorname{Spec} R$ (an ideal sheaf datum on $C \times_R \operatorname{Spec} R$ whose closed subscheme is finite, flat and locally of finite presentation over the base with fibre rank $e$); third, that for every algebraically closed field $k$, every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ and every cover of the fibre by two affine opens with affine intersection, the two-chart Čech Euler characteristic $\dim_k H^0 - \dim_k H^1$ of the fibre pullback of $\mathrm{sectionTwist}\,r \otimes D_\gamma.\mathrm{idealModule}$ (the dual of the $r$-th power of the ideal of the section, tensored with the ideal module of $D_\gamma$) equals $1$. Then there are a scheme $X$ and a morphism $f$ from the Yoneda presheaf of $X$ to the total presheaf of $\mathrm{relSubPicPresheaf}\ c\ \varepsilon\ (\mathrm{algEquivZeroCut}\ c\ \varepsilon)$ — equivalently, by `uliftYonedaEquiv`, a structure morphism $X \to \operatorname{Spec} R$ together with a class of rigidified line bundles on $C \times_R X$ all of whose geometric fibres are algebraically equivalent to zero — such that this structure morphism is locally of finite type, and such that for every scheme $T$ and every element $x$ of the same total presheaf at $T$, with structure morphism $t = (\mathrm{uliftYonedaEquiv}\ x).1$ locally of finite type, there are an open subscheme $U$ of $T$ and a morphism $\varphi : U \to X$ with the following three properties. (i) For every rigidified line bundle $L$ on $C \times_R T$ whose class is the given element of the presheaf, every field $k$ and every $s : \operatorname{Spec} k \to T$, the range of $s$ lies in $U$ if and only if for every cover of the fibre $(C \times_R T) \times_T \operatorname{Spec} k$ by two affine opens with affine intersection the two-chart Čech $H^1$ of the fibre pullback of $L.L \otimes (\mathrm{sectionTwist}\ r \otimes (D_\gamma$ pulled back along $t)\mathrm{.idealModule})$ is a subsingleton. (ii) $\varphi$ followed by $f$ equals the open immersion $U \hookrightarrow T$ followed by $x$. (iii) For every scheme $T'$, every $\psi : T' \to T$ with $\psi$ followed by $t$ locally of finite type and every $\varphi' : T' \to X$ with $\varphi'$ followed by $f$ equal to $\psi$ followed by $x$, there is $\chi : T' \to U$ with $\chi$ followed by $U \hookrightarrow T$ equal to $\psi$ and $\chi$ followed by $\varphi$ equal to $\varphi'$.
--
--   This is Milne's chart $J^{\gamma} \to \operatorname{Pic}^0$ attached to a single divisor $D_\gamma$ of degree $e$ and the twist by $r\varepsilon$: the locus where the relevant $H^1$ vanishes on all field-valued fibres is open, is cut out by $\varphi$, and $\varphi$ is universal among finite-type test objects, so that the chart is relatively representable by an open immersion against test schemes locally of finite type over the Noetherian base. It feeds the assembly of several such charts into a covering of the rigidified relative Picard functor over a reduced base in `exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U : Set T) ↔
                ∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U, χ ≫ U.ι = ψ ∧ χ ≫ φ = φ' := by sorry
