-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/727dc055-84f7-5ea1-a627-cb9332d396e1
-- title:
--   Block general position at a two-line degenerate geometric fibre
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a proper morphism and $\varepsilon$ a section of $c$. Let $B_0,\dots,B_{M-1}$ be $R$-algebras with morphisms $z_i\colon\operatorname{Spec}B_i\to C$ over $R$ whose images are pairwise disjoint, let $\deg\colon\mathrm{Fin}\,M\to\mathbb N$ satisfy $1\le\deg i\le b$, and let $r,g$ satisfy $2g\le r+1$ and $r\,b^{\,r-g}+(r-g)<M$. Let $\Omega$ be an algebraically closed $R$-algebra field for which the $R$-algebra maps $B_i\to\Omega$ are in bijection with $\mathrm{Fin}(\deg i)$, write $C_\Omega=C\times_{\operatorname{Spec}R}\operatorname{Spec}\Omega$, and assume $C_\Omega$ is proper over $\Omega$, reduced, and not smooth. Let $U\subseteq C$ be open with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$ and $\varepsilon$ landing in $U$. Assume a two-line degeneration hypothesis `hbad`: for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ with non-smooth fibre, $C_k$ is the union of the images of two closed immersions $i_1,i_2$ of `CurveModel k (RatFunc k)`s over $k$ (integral proper smooth relative-dimension-one schemes with function field $k(T)$ and closed points in bijection with the places of $k(T)/k$), glued along finitely many pairs of points $T=a_\iota$, $T=b_\iota$ with $a$ injective and these the only coincidences, with $\operatorname{pullback} i_1\,i_2$ reduced, together with a two-affine open cover of $C_k$ cutting out on each model the complements of $T=\infty$ and $T=0$; moreover $i_1$ sends $T=\infty$ to the $\varepsilon$-point of the fibre, the image of $i_1$ meets the preimage of $U$ exactly in the connected component through that point, the glueing points are precisely the points outside the preimage of $U$, and the complement of the image of $i_2$ is open with $i_1$ restricting to an open immersion over it. Assume further that each $z_i$ meets $C_\Omega$ inside that connected component, that every two-affine open cover of $C_\Omega$ gives Čech cohomology of the structure sheaf with $\dim_\Omega\check H^0=1$ and $\dim_\Omega\check H^1=g$, and let $L_0$ be an invertible module on $C_\Omega$ which is algebraically equivalent to zero in the sense of `IsAlgEquivZero` (trivialised at one $\Omega$-point and isomorphic to $L_0$ at another, along an invertible module on a geometrically integral base locally of finite type). Then there is an injective $a\colon\mathrm{Fin}(r-g)\to\mathrm{Fin}\,M$ such that for every family $v_1,\dots,v_{r-g}$ of $\Omega$-points of $C_\Omega$ (sections of $C_\Omega\to\operatorname{Spec}\Omega$), each $v_j$ factoring through $z_{a(j)}$ via some $R$-algebra map $B_{a(j)}\to\Omega$, and for every two-affine open cover $\mathcal W$ of $C_\Omega$, the Čech $\check H^1$ of $L_0\otimes(\mathcal I_{\varepsilon_\Omega}^{\,r})^{\vee}\otimes\prod_j\mathcal I_{v_j}$ computed on $\mathcal W$ is a subsingleton, where $\mathcal I^{\vee}$ denotes the dual of the ideal-sheaf module.
--
--   This is the general-position statement for the relative $\operatorname{Pic}^0$ construction at a geometric fibre which degenerates into two rational curves glued at finitely many nodes: it produces a transversal of the rational blocks, on the component through the section, for which the twisted degree-zero bundle $L_0(r\varepsilon-v_1-\dots-v_{r-g})$ has vanishing first Čech cohomology. It is used by [`AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_pool_of_bijective_sections), which assembles the fibrewise charts of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicCurve AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_twoLineDegeneration_of_sectionInSmoothLocus
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b)
    (r g : ℕ) (hr : 2 * g ≤ r + 1) (hcount : r * b ^ (r - g) + (r - g) < M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i))
    [IsProper (pullback.snd c (SmoothProperCurve.specMap R Ω))]
    [IsReduced (pullback c (SmoothProperCurve.specMap R Ω))]

    (hns : ¬ Smooth (pullback.snd c (SmoothProperCurve.specMap R Ω)))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))
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

    (hzε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base ⊆
      connectedComponentIn
        (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (hH0 : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω ↥(𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H0 = 1)
    (hg : ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
      Module.finrank Ω (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
        (SheafOfModules.unit (pullback c (SmoothProperCurve.specMap R Ω)).ringCatSheaf)).H1 = g)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
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
