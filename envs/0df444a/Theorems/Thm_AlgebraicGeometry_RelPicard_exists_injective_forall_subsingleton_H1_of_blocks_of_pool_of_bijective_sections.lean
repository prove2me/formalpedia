-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/45644568-f3a0-5692-8ec0-163fedadd18d
-- title:
--   Block general position for a split pool on geometric fibres
-- statement:
--   Let $R$ be a commutative ring and $c\colon C\to\operatorname{Spec}R$ a proper flat morphism of schemes such that for every $R$-algebra $A$ the structure map $A\to\Gamma(C\times_{\operatorname{Spec}R}\operatorname{Spec}A,\top)$ is bijective. Fix a section $\varepsilon$ of $c$ (a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity) and an open subscheme $U\subseteq C$ with $U\hookrightarrow C$ followed by $c$ smooth of relative dimension $1$, such that the image of $\varepsilon$ lies in $U$, the image of every smooth geometric fibre lies in $U$, and every geometric fibre $C_x$ ($x\colon\operatorname{Spec}k\to\operatorname{Spec}R$, $k$ algebraically closed) is reduced. Fix $g\in\mathbb N$ such that for every such $k$, every $x$ and every two-chart affine open cover of the fibre, the Čech $H^1$ of the structure sheaf (the quotient of the sections over the intersection by the image of the difference of the two restrictions) has $k$-dimension $g$. Assume that every non-smooth geometric fibre $C_s$ is a gluing of two projective lines in the following explicit sense: there are curve models $M_1,M_2$ of $k(t)$ over $k$ (integral proper schemes, smooth of relative dimension $1$, with function field identified with $k(t)$ and closed points in bijection with the places), closed immersions $i_1,i_2$ into $C_s$ over $\operatorname{Spec}k$ whose images cover $C_s$, an injective $a\colon\operatorname{Fin}n\to k^{\times}$, a further $b\colon\operatorname{Fin}n\to k^{\times}$ and a two-chart affine open cover $\mathcal W_0$ of $C_s$, such that the point of $M_1$ at the place $t=a_i$ is identified with the point of $M_2$ at $t=b_i$, these are the only identifications, $M_1\times_{C_s}M_2$ is reduced, the two charts of $\mathcal W_0$ pull back on each $M_j$ to the complements of the places $t=\infty$ and $t=0$, the place $t=\infty$ of $M_1$ maps to the point of $C_s$ cut out by $\varepsilon$, the image of $i_1$ meets the preimage of $U$ exactly in the connected component of that preimage through the $\varepsilon$-point, the singular points are precisely the points outside the preimage of $U$, and the complement of the image of $i_2$ is open with $i_1$ an open immersion over it. Let $A$ be a finite faithfully flat $R$-algebra, $r\in\mathbb N$ with $2g\le r+1$, and $B_0,\dots,B_{M-1}$ finite étale $R$-algebras with degrees $\deg i\ge 1$ and $A$-algebra isomorphisms $A\otimes_R B_i\cong A^{\deg i}$, given by closed immersions $z_i\colon\operatorname{Spec}B_i\to C$ over $\operatorname{Spec}R$ with pairwise disjoint images contained in $U$ and such that on every geometric fibre the preimage of the image of $z_i$ lies in the connected component of the preimage of $U$ through the $\varepsilon$-point; let $b$ bound all $\deg i$ and assume $r\,b^{\,r-g}+(r-g)<M$. Then for every algebraically closed $R$-algebra field $\Omega$ and every invertible module $L_0$ on $C_\Omega=C\times_{\operatorname{Spec}R}\operatorname{Spec}\Omega$ satisfying `IsAlgEquivZero` for the projection to $\operatorname{Spec}\Omega$ (algebraic equivalence to zero, witnessed by an invertible module on a base change along a geometrically integral morphism locally of finite type together with two sections specialising it to the unit and to $L_0$), there is an injective $a\colon\operatorname{Fin}(r-g)\to\operatorname{Fin}M$ such that for every family $v_0,\dots,v_{r-g-1}$ of sections of $C_\Omega\to\operatorname{Spec}\Omega$ for which each $v_j$ factors through $z_{a(j)}$ via some $R$-algebra homomorphism $B_{a(j)}\to\Omega$, and for every two-chart affine open cover $\mathcal W$ of $C_\Omega$, the Čech $H^1$ of $L_0\otimes(\mathcal I_{\varepsilon_\Omega}^{\,r})^{\vee}\otimes\prod_j\mathcal I_{v_j}$ over $\mathcal W$ is a subsingleton, where $\mathcal I$ denotes the ideal-sheaf module of a section and $(\cdot)^{\vee}$ the dual.
--
--   This is the general-position statement for a pool of disjoint finite étale "blocks" on a curve over a base: a suitably large supply of blocks contains an injective $(r-g)$-tuple all of whose transversals give charts with vanishing first cohomology for $L_0(r\varepsilon-\sum v_j)$, uniformly over all geometric points of the base. It is the hypothesis consumed by the representability result for the algebraic-equivalence-zero part of the relative Picard functor after base change, in the construction of the relative Jacobian for curves whose degenerate fibres are transversal gluings of two projective lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [Flat c]
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεA : Set.range ε.1 ⊆ (U : Set C))
    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x))
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback c s) (i₂ : M₂.C ⟶ pullback c s)
        (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
        (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback c s).TwoAffineOpenCover),
        i₁ ≫ pullback.snd c s = M₁.toBase ∧ i₂ ≫ pullback.snd c s = M₂.toBase ∧
        Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
        Function.Injective a ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
          i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        (∀ (p : M₁.C) (q : M₂.C), i₁.base p = i₂.base q →
          ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
            q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
        IsReduced (pullback i₁ i₂) ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
        ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
          {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
          {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
        i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∧
        Set.range i₁.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
          (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∀ y : ↥(pullback c s),
          (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
            y ∈ (pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.base)ᶜ ∧
          IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)))
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.FaithfullyFlat R A]
    (r : ℕ) (hgr : 2 * g ≤ r + 1)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i : Fin M),
      (pullback.fst c s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)))
    (b : ℕ) (hdegb : ∀ i, deg i ≤ b) (hMlt : r * b ^ (r - g) + (r - g) < M) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
      (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules), Scheme.Modules.IsInvertible L₀ →
      IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀ →
      ∃ a : Fin (r - g) → Fin M, Function.Injective a ∧
        ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
            q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
          (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
            (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
              Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
          ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
            Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
                (∏ j, (v j).1.ker).module))).H1 := by sorry
