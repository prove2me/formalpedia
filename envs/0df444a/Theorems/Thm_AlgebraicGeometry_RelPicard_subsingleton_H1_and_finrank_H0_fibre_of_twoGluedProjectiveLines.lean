-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines
-- name    : AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c5570e6d-4d94-576b-9a8d-5db9d315a69e
-- title:
--   Vanishing H¹ and h⁰=1 on a two-line fibre
-- statement:
--   Fix a commutative ring $R$ and a separated morphism $c : C \to \operatorname{Spec} R$, an open $U \subseteq C$ such that $U \hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$, and a section $\varepsilon$ of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity) whose image lies in $U$. Let $t : T \to \operatorname{Spec} R$, let $D$ be a relative effective Cartier divisor of degree $e$ for $c$ over $t$ — an ideal sheaf $D.I$ on $\operatorname{pullback} c\,t$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ with all fibre ranks $e$ — with support contained in the preimage of $U$. Let $K$ be an algebraically closed field and $\mathrm{pt} : \operatorname{Spec} K \to T$ a point such that the fibre $X = \operatorname{pullback}(\operatorname{pullback.snd} c\,t)\,\mathrm{pt}$ is reduced and the structure morphism $\mathrm{fibreAt}\,c\,t\,\mathrm{pt} = \operatorname{pullback.snd} : X \to \operatorname{Spec} K$ is separated. Let $M_1, M_2$ be curve models of $\mathrm{RatFunc}\,K$ over $K$ (integral schemes, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$, with function field identified with $K(x)$ over $K$ and closed points in bijection `placeEquiv` with the places of $K(x)/K$, the stalks matching the valuation subrings, and every finite set of points contained in an affine open), and let $i_1 : M_1.C \to X$, $i_2 : M_2.C \to X$ be closed immersions over $\operatorname{Spec} K$ (i.e. $i_k$ followed by $\mathrm{fibreAt}$ is $M_k.\mathrm{toBase}$) whose images cover $X$. Assume given $g \in \mathbb{N}$ and $a, b : \mathrm{Fin}(g+1) \to K^\times$ with $a$ injective such that for each $j$ the point of $M_1.C$ at the place $x = a_j$ and the point of $M_2.C$ at the place $x = b_j$ have the same image in $X$, that these are the only coincidences $i_1(p) = i_2(q)$, and that $\operatorname{pullback} i_1\, i_2$ is reduced. Assume a two-affine open cover $\mathcal{W}_0$ of $X$ (two affine opens with affine intersection covering $X$) whose first member pulls back on $M_1.C$ and $M_2.C$ to the complement of the point at infinity and whose second pulls back to the complement of the point $x = 0$, and arbitrary two-affine open covers $\mathcal{V}_1$ of $M_1.C$ and $\mathcal{V}_2$ of $M_2.C$. Assume further an open $W_1 \subseteq X$ with $(i_1^{-1}W_1) \hookrightarrow M_1.C$ followed by $i_1$ an open immersion and $W_1$ contained in the image of $i_1$, such that every point of $X$ whose image under $\operatorname{pullback.fst}$ lies in the support of $D.I$ or in the image of the rigidifying section $\mathrm{rigSection}\,c\,t\,\varepsilon$ lies in $W_1$, while no point of $M_2.C$ has its image under $i_2$ then $\operatorname{pullback.fst}$ in the support of $D.I$ or in the image of that section; and $g + e = r$. Finally let $L$ be a rigidified line bundle for $(c, \varepsilon, t)$ (an invertible module $L.L$ on $\operatorname{pullback} c\,t$ trivialised along $\mathrm{rigSection}$) satisfying $\mathrm{FibrewiseAlgEquivZero}$, i.e. for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$ the restriction of $L.L$ to the fibre over $s$ satisfies $\mathrm{IsAlgEquivZero}$, and assume that the fibre module at $\mathrm{pt}$ of $L.L \otimes (\mathrm{sectionTwist}\,c\,\varepsilon\,t\,r \otimes D.\mathrm{idealModule})$ — where $\mathrm{sectionTwist}$ is the dual of the $r$-th power of the ideal sheaf of the section and $D.\mathrm{idealModule}$ is the module of the ideal sheaf of $D$ — is invertible. Then for every two-affine open cover $\mathcal{W}$ of $X$, the two-term Čech complex of sections of that fibre module over $\mathcal{W}$, regarded over $K$, has $H^1$ (the quotient of the sections on the intersection by the image of the difference map) a subsingleton, and its $H^0$ (the kernel of that map on the product of the sections over the two charts) of $K$-dimension $1$.
--
--   This is the cohomological input at a geometric fibre that degenerates into two rational curves glued at $g+1$ nodes: a line bundle algebraically equivalent to zero on such a fibre, twisted by $r\varepsilon$ and by $-D$ with $r = g+e$, has no first Čech cohomology and a one-dimensional space of sections, computed on an arbitrary two-chart affine cover. It supplies the chart hypothesis used by [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_not_smooth) in the construction of charts for the relative Picard functor at non-smooth fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_of_twoGluedProjectiveLines
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {r e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] (pt : Spec (CommRingCat.of K) ⟶ T)
    [IsReduced (pullback (pullback.snd c t) pt)] [IsSeparated (fibreAt c t pt)]

    (M₁ M₂ : CurveModel K (RatFunc K))
    (i₁ : M₁.C ⟶ pullback (pullback.snd c t) pt) (i₂ : M₂.C ⟶ pullback (pullback.snd c t) pt)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ fibreAt c t pt = M₁.toBase) (hi₂ : i₂ ≫ fibreAt c t pt = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)

    (g : ℕ) (a b : Fin (g + 1) → Kˣ) (ha : Function.Injective a)
    (hnode : ∀ j, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint K (a j : K))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint K (b j : K))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ j, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint K (a j : K))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint K (b j : K))).1)
    (htrans : IsReduced (pullback i₁ i₂))

    (𝒲₀ : (pullback (pullback.snd c t) pt).TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty K)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty K)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) = {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) = {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1}ᶜ)

    (𝒱₁ : M₁.C.TwoAffineOpenCover) (𝒱₂ : M₂.C.TwoAffineOpenCover)

    (W₁ : (pullback (pullback.snd c t) pt).Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]
    (hW₁ : (W₁ : Set ↥(pullback (pullback.snd c t) pt)) ⊆ Set.range i₁.base)
    (hD : ∀ y : ↥(pullback (pullback.snd c t) pt), (pullback.fst (pullback.snd c t) pt).base y ∈ D.I.support → y ∈ W₁)
    (hε : ∀ y : ↥(pullback (pullback.snd c t) pt),
      (pullback.fst (pullback.snd c t) pt).base y ∈ Set.range (rigSection c t ε).base → y ∈ W₁)
    (hD₂ : ∀ y : M₂.C, (pullback.fst (pullback.snd c t) pt).base (i₂.base y) ∉ D.I.support)
    (hε₂ : ∀ y : M₂.C, (pullback.fst (pullback.snd c t) pt).base (i₂.base y) ∉ Set.range (rigSection c t ε).base)
    (hr : g + e = r)

    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (hinv : Scheme.Modules.IsInvertible (fibreModule c t pt (L.L ⊗ (sectionTwist c ε t r ⊗ D.idealModule)))) :
    ∀ 𝒲 : (pullback (pullback.snd c t) pt).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t pt) (fibreModule c t pt (L.L ⊗ (sectionTwist c ε t r ⊗ D.idealModule)))).H1 ∧
      Module.finrank K (𝒲.sectionsOf (fibreAt c t pt) (fibreModule c t pt (L.L ⊗ (sectionTwist c ε t r ⊗ D.idealModule)))).H0 = 1 := by sorry
