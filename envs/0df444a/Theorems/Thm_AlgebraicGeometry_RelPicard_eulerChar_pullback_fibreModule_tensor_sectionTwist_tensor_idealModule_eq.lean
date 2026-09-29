-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq
-- name    : AlgebraicGeometry.RelPicard.eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/679e6d63-5af2-5975-bb0f-edf295e51e58
-- title:
--   Euler characteristic of L(rε-D) on a fibre component
-- statement:
--   Let $R$ be a commutative ring and $c : C \to \operatorname{Spec} R$ a separated morphism of schemes, let $U \subseteq C$ be an open whose structure morphism $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c$ the identity) whose image lies in $U$. Let $t : T \to \operatorname{Spec} R$ be a base, $r, e$ natural numbers, and $D$ a relative effective Cartier divisor of degree $e$ for $c$ over $t$: an ideal sheaf datum $D.I$ on $C \times_R T$ whose closed subscheme is finite, flat and locally of finite presentation over $T$ with fibre rank $e$ at every point of $T$, and with support contained in the preimage of $U$ under the first projection. Let $k$ be an algebraically closed field, $pt : \operatorname{Spec} k \to T$ a point, and write $X = (C \times_R T) \times_T \operatorname{Spec} k$ for the fibre, $\mathrm{fibreAt}$ being its projection to $\operatorname{Spec} k$. Let $F_1$ be a field extension of $k$ and $M_1$ a `CurveModel k F₁`, i.e. an integral scheme $M_1.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, with a ring isomorphism of $F_1$ onto its function field compatible with $k$, a bijection of its closed points with the places of $F_1/k$ matching stalks with valuation rings, and every finite set of points contained in an affine open. Let $i_1 : M_1.C \to X$ be a morphism over $\operatorname{Spec} k$, and $W_1 \subseteq X$ an open contained in the set-theoretic image of $i_1$ and such that $i_1$ restricted to $i_1^{-1}W_1$ is an open immersion; assume every point of $X$ whose image under the first projection to $C \times_R T$ lies in the support of $D.I$, or in the image of the rigidifying section $\mathrm{rigSection}\,c\,t\,\varepsilon : T \to C \times_R T$ determined by $t \circ \varepsilon$ and the identity of $T$, lies in $W_1$. Let $LL$ be an invertible module on $C \times_R T$ (every point has a neighbourhood on which $LL$ restricts to the unit module), and assume that for every two-affine open cover $\mathcal{W}'$ of $M_1.C$ — two affine opens covering $M_1.C$ with affine intersection — the associated two-term Čech complex of $i_1^{*}$ of the fibre module of $LL$ satisfies $\dim_k H^0 - \dim_k H^1 = 1$. Finally let $g, s$ be natural numbers with $g + e = r$ and $s = g + 1$. Then for every two-affine open cover $\mathcal{W}'$ of $M_1.C$, the corresponding Čech complex of $i_1^{*}$ of the fibre module of $LL \otimes (\mathrm{sectionTwist}\,c\,\varepsilon\,t\,r \otimes D.\mathrm{idealModule})$ — where $\mathrm{sectionTwist}$ is the inverse module of the $r$-th power of the section ideal of $\varepsilon$ and $D.\mathrm{idealModule}$ is the module of $D.I$ — satisfies $\dim_k H^0 - \dim_k H^1 = s$.
--
--   This is the Riemann–Roch bookkeeping step asserting that twisting an invertible module by $r\varepsilon - D$ raises the Euler characteristic of its restriction to a smooth component of a geometric fibre by $r - e$, the Euler characteristic being computed by a two-chart Čech complex. It feeds the line-by-line computations of Euler characteristics on degenerate fibres and, through them, the representability statements for the relative Picard functor used in the Néron model constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.eulerChar_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {r e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    {k : Type u} [Field k] [IsAlgClosed k] (pt : Spec (CommRingCat.of k) ⟶ T)

    {F₁ : Type u} [Field F₁] [Algebra k F₁] (M₁ : CurveModel k F₁)
    (i₁ : M₁.C ⟶ pullback (pullback.snd c t) pt) (hi₁ : i₁ ≫ fibreAt c t pt = M₁.toBase)
    (W₁ : (pullback (pullback.snd c t) pt).Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]
    (hW₁ : (W₁ : Set ↥(pullback (pullback.snd c t) pt)) ⊆ Set.range i₁.base)

    (hD : ∀ y : ↥(pullback (pullback.snd c t) pt), (pullback.fst (pullback.snd c t) pt).base y ∈ D.I.support → y ∈ W₁)
    (hε : ∀ y : ↥(pullback (pullback.snd c t) pt), (pullback.fst (pullback.snd c t) pt).base y ∈ Set.range (rigSection c t ε).base → y ∈ W₁)

    (LL : (pullback c t).Modules) (hLL : Scheme.Modules.IsInvertible LL)
    (hLL₁ : ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (fibreModule c t pt LL))).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (fibreModule c t pt LL))).H1 = 1)
    (g s : ℕ) (hr : g + e = r) (hs : s = g + 1) :
    ∀ 𝒲' : M₁.C.TwoAffineOpenCover,
      (Module.finrank k ↥(𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (fibreModule c t pt (LL ⊗ (sectionTwist c ε t r ⊗ D.idealModule))))).H0 : ℤ) -
        Module.finrank k (𝒲'.sectionsOf M₁.toBase ((Scheme.Modules.pullback i₁).obj (fibreModule c t pt (LL ⊗ (sectionTwist c ε t r ⊗ D.idealModule))))).H1 = s := by sorry
