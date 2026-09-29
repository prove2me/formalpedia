-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/98786575-88f6-541f-b689-45b67f728b37
-- title:
--   Far blocks giving check H¹=0 and h⁰=1 on C₂
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ proper with a section $\varepsilon$ (a morphism with $\varepsilon\circ c$ the identity), and $U\subseteq C$ an open whose structure morphism to $\operatorname{Spec}R$ is smooth of relative dimension $1$ and contains the image of $\varepsilon$. Fix $M'$ disjointly placed "blocks": $R$-algebras $B'_i$ with morphisms $z'_i\colon\operatorname{Spec}B'_i\to C$ over $R$ having pairwise disjoint images, degrees $\deg'_i\le b$ with $1\le b$, and an algebraically closed field $\Omega$ over $R$ with bijections $(B'_i\to_R\Omega)\simeq\operatorname{Fin}(\deg'_i)$. Write $X=C\times_{\operatorname{Spec}R}\operatorname{Spec}\Omega$, $U_\Omega$ for the preimage of $U$ under the first projection, and $\varepsilon_\Omega$ for the base-changed section. Let $c_1,c_2$ be proper, smooth of relative dimension $1$ and geometrically integral over $\Omega$, with closed immersions $i_1,i_2$ into $X$ over $\operatorname{Spec}\Omega$. The hypothesis `hbadΩ` packages the degeneration data, summarised: the ranges of $i_1,i_2$ cover $X$; the scheme-theoretic intersection $C_1\times_XC_2$ is reduced with exactly $n>0$ points, $n>0$; the point of $\varepsilon_\Omega$ lies on $i_1$ and off $i_2$; $U_\Omega$ is precisely the complement of the image of the crossing locus; the trace of $i_1$ on $U_\Omega$ is the connected component of the $\varepsilon_\Omega$-point, and that of $i_2$ is its complement in $U_\Omega$; and each $i_k$ restricted over an open with underlying set the complement of the other range is an open immersion. Further, `hz'ε` requires each block $z'_i$ to lie fibrewise inside $U_\Omega$ off the $\varepsilon_\Omega$-component. Fix $r',\gamma_2,e_2$, an index $i_0$, and a two-affine open cover $\mathcal V_2$ of $C_2$ (two affine opens with affine intersection covering $C_2$) with $\dim_\Omega$ of the two-chart Čech $H^1$ of the structure sheaf equal to $\gamma_2$, together with $\gamma_2+e_2=r'\deg'_{i_0}$, $2\gamma_2\le r'\deg'_{i_0}$ and the counting bound $(n+1)(r'b)b^{e_2}+e_2+1<M'$; let $q_m$, $m\in\operatorname{Fin}(\deg'_{i_0})$, be the $\Omega$-points of $X$ cut out by the $\Omega$-points of the block $z'_{i_0}$ under the given bijection. Finally let $r\in\mathbb N$ and let $L_0$ be an invertible module on $X$ satisfying `IsAlgEquivZero` for the projection to $\operatorname{Spec}\Omega$, i.e. algebraically equivalent to zero in the sense that $L_0$ and the unit are the two specialisations of an invertible module over a geometrically integral base of finite type. The conclusion asserts the existence of an injective $a'\colon\operatorname{Fin}e_2\to\operatorname{Fin}M'$ avoiding $i_0$ such that for every tuple $v'$ of $\Omega$-points of $X$ with $v'_j$ factoring through $z'_{a'(j)}$ via some $R$-algebra map $B'_{a'(j)}\to\Omega$, every $e_1$ and every tuple $v$ of $\Omega$-points of $X$ whose images lie in $U_\Omega$ off the range of $i_2$, and every two-affine open cover $\mathcal W_2$ of $C_2$, the module $\mathcal M=i_2^*\bigl(L_0\otimes(\ker\varepsilon_\Omega^{\,r}\cdot(\prod_m\ker q_m)^{r'})^{\vee}\otimes(\prod_j\ker v_j\cdot\prod_j\ker v'_j)\bigr)$ — the dual of the module of the indicated ideal sheaf tensored with the module of the product ideal sheaf — has vanishing (subsingleton) two-chart Čech $H^1$ on $\mathcal W_2$, has $\dim_\Omega H^0=1$, and for every $\Omega$-point $p$ of $C_2$ whose image in $X$ lies on the range of $i_1$ one has $\dim_\Omega H^0(\mathcal M\otimes(\ker p))=0$.
--
--   This is the $C_2$-side half of the block general position statement at a geometric fibre degenerating into two smooth curves meeting transversally in $n$ points: after twisting by the blocks indexed by $a'$, the restriction to the second component has $h^1=0$, $h^0=1$, and its unique section vanishes at none of the $n$ crossing points. It is used in the two-sided version, where the data on $C_1$ and on $C_2$ are combined to control sections on the whole degenerate fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {M' : ℕ} (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C)
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hz'disj : Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base))
    (deg' : Fin M' → ℕ) {b : ℕ} (hb : 1 ≤ b) (hdeg'b : ∀ i, deg' i ≤ b)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB' : ∀ i, (B' i →ₐ[R] Ω) ≃ Fin (deg' i))

    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of Ω)) (c₂ : C₂ ⟶ Spec (CommRingCat.of Ω))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (pullback.snd c (SmoothProperCurve.specMap R Ω))) (i₂ : SchemeHomOver c₂ (pullback.snd c (SmoothProperCurve.specMap R Ω)))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1] (n : ℕ)
    (hbadΩ :
        (∀ z : ↥(pullback c (SmoothProperCurve.specMap R Ω)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) =
          connectedComponentIn ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
            (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) =
          ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \
            connectedComponentIn ((pullback.fst c (SmoothProperCurve.specMap R Ω) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
              (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)) ∧
        (∃ W₁ : (pullback c (SmoothProperCurve.specMap R Ω)).Opens, (W₁ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c (SmoothProperCurve.specMap R Ω)).Opens, (W₂ : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))

    (hz'ε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z' i).base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \
        connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
          (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (r' γ₂ e₂ : ℕ) (i₀ : Fin M') (𝒱₂ : C₂.TwoAffineOpenCover)
    (hγ₂ : Module.finrank Ω (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf)).H1 = γ₂)
    (he₂ : γ₂ + e₂ = r' * deg' i₀) (hr₂ : 2 * γ₂ ≤ r' * deg' i₀)
    (hcount₂ : (n + 1) * (r' * b) * b ^ e₂ + e₂ + 1 < M')

    (q : Fin (deg' i₀) → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
    (hq : ∀ m, (q m).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
      Spec.map (CommRingCat.ofHom ((eB' i₀).symm m).toRingHom) ≫ z' i₀)

    (r : ℕ)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a' : Fin e₂ → Fin M', Function.Injective a' ∧ (∀ j, a' j ≠ i₀) ∧
      ∀ (v' : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        (∀ j, ∃ ψ : B' (a' j) →ₐ[R] Ω,
          (v' j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z' (a' j)) →
        ∀ {e₁ : ℕ} (v : Fin e₁ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, Set.range (v j).1.base ⊆
            (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₂.1.base) →
          ∀ 𝒲₂ : C₂.TwoAffineOpenCover,
            (Subsingleton (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj
                (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)))).H1 ∧
              Module.finrank Ω (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj
                (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)))).H0 = 1) ∧
            ∀ p : Spec (CommRingCat.of Ω) ⟶ C₂, p ≫ c₂ = 𝟙 _ →
              Set.range (p ≫ i₂.1).base ⊆ Set.range i₁.1.base →
              Module.finrank Ω (𝒲₂.sectionsOf c₂ ((Scheme.Modules.pullback i₂.1).obj
                (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗ (p.ker).module)).H0 = 0 := by sorry
