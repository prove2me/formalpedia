-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/90b3eabd-c641-5176-940c-6b8d78980789
-- title:
--   Zeros of a section on two glued rational curves
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper morphism of schemes, $U$ an open of $C$, $k$ an algebraically closed field and $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ a morphism such that the fibre $P:=C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ is reduced. Let $M_1,M_2$ be curve models of $\operatorname{RatFunc}k$ over $k$ (integral schemes with a proper smooth morphism of relative dimension $1$ to $\operatorname{Spec}k$, an isomorphism of the function field with $k(T)$ over $k$, a bijection `placeOfPoint` from closed points to places of $k(T)/k$ matching stalks with valuation subrings, and every finite set of points contained in an affine open), and let $i_1\colon M_1.C\to P$, $i_2\colon M_2.C\to P$ be closed immersions with $i_j$ followed by the projection to $C$'s base change equal to the structure morphism $M_j.\mathrm{toBase}$, whose images cover $P$. Let $a,b\colon \mathrm{Fin}\,s\to k^{\times}$ with $s>0$ and $a$ injective, assume that for each $i$ the point of $M_1.C$ with place `placeOfPoint k (a i)` and the point of $M_2.C$ with place `placeOfPoint k (b i)` have the same image in $P$, that these are the only coincidences of images of points of $M_1.C$ and $M_2.C$, and that $M_1.C\times_P M_2.C$ is reduced. Let $\mathcal W_0$ be a two-chart affine open cover of $P$ (two affine opens with affine intersection whose union is $P$) whose traces on $M_1.C$ and $M_2.C$ are the complements of the point at the place at infinity (first chart) and of the point at the place of $0$ (second chart). Assume an open $W_1\subseteq P$ exists with underlying set the complement of the image of $i_2$ and with the inclusion of $i_1^{-1}W_1$ followed by $i_1$ an open immersion, and that every point of $M_1.C$ distinct from all the node points $a_i$ maps into $U$ under the projection $P\to C$. Let $g\in\mathbb N$ be the $k$-dimension of the first Čech cohomology $H^1$ of the structure sheaf on $\mathcal W_0$ (the overlap sections modulo the image of the Čech differential). Finally let $M$ be a module on $P$ that is invertible (each point has a neighbourhood on which $M$ pulls back to the unit sheaf), with $i_2^{*}M$ isomorphic to $i_2^{*}\mathcal O_P$, with $\dim_k H^0(\mathcal W_0,M)=1$ and $H^1(\mathcal W_0,M)$ a subsingleton, and let $\sigma\colon \mathbf 1\to M$ be a nonzero morphism. Then there is a relative effective Cartier divisor $D_x$ for $c$ of degree $g$ over $x$, i.e. an ideal sheaf datum $\mathcal I$ on $P$ whose subscheme inclusion followed by the projection to $\operatorname{Spec}k$ is finite, flat and locally of finite presentation with fibre rank $g$ at every point, such that $\mathcal I$ equals the zero-scheme ideal of $\sigma$ (the infimum of the ideal sheaf data dominating the coefficient ideals of $\sigma$ on all affine opens) and the support of $\mathcal I$ is contained in the preimage of $U$ under the projection $P\to C$.
--
--   This is the geometry of line bundles of bidegree $(g,0)$ on a fibre consisting of two smooth rational curves crossing transversally at $s=g+1$ points, as in the Deligne–Rapoport description of the special fibre of a modular curve: such a bundle has a one-dimensional space of sections, and the zero scheme of a nonzero section is a degree-$g$ relative effective Cartier divisor lying on the first component away from the nodes. It is used in the construction of relative effective Cartier divisors representing points of the relative Picard functor on non-smooth reduced fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicCurve

universe u

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (U : C.Opens)
    (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) [IsReduced (pullback c x)]

    (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c x) (i₂ : M₂.C ⟶ pullback c x)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ pullback.snd c x = M₁.toBase) (hi₂ : i₂ ≫ pullback.snd c x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → kˣ) (hs : 0 < s) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
      i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (hinter : ∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (𝒲₀ : (pullback c x).TwoAffineOpenCover)
    (hU0₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU0₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ)
    (hU1₁ : ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
      {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)
    (hU1₂ : ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
      {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ)

    (hW₁ : ∃ W₁ : (pullback c x).Opens, (W₁ : Set ↥(pullback c x)) = (Set.range i₂.base)ᶜ ∧
      IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))

    (hU₁ : ∀ p : M₁.C, (∀ i, p ≠ (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
      (pullback.fst c x).base (i₁.base p) ∈ U)

    (g : ℕ)
    (hg : Module.finrank k (𝒲₀.sectionsOf (pullback.snd c x)
      (SheafOfModules.unit (pullback c x).ringCatSheaf)).H1 = g)

    (M : (pullback c x).Modules) (hMinv : Scheme.Modules.IsInvertible M)
    (hM₂ : Nonempty ((Scheme.Modules.pullback i₂).obj M ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback c x).ringCatSheaf)))
    (hM : Module.finrank k ↥(𝒲₀.sectionsOf (pullback.snd c x) M).H0 = 1 ∧
      Subsingleton (𝒲₀.sectionsOf (pullback.snd c x) M).H1)
    (σ : 𝟙_ (pullback c x).Modules ⟶ M) (hσ : σ ≠ 0) :
    ∃ Dx : RelEffCartierDiv c g x, Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U := by sorry
