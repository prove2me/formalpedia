-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3ecd620e-f9be-5cc9-ad42-5606bde3c0db
-- title:
--   Near-side general position at a two-component degenerate fibre
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a proper morphism, $\varepsilon$ a section of $c$, and $U \subseteq C$ an open whose structure morphism $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$, with the image of $\varepsilon$ inside $U$. Given $M$ commutative $R$-algebras $B_i$ ($i \in \mathrm{Fin}\,M$) together with $R$-morphisms $z_i : \operatorname{Spec} B_i \to C$ having pairwise disjoint images, numbers $\deg i \le b$ with $1 \le b$, an algebraically closed $R$-algebra field $\Omega$, and bijections $(B_i \to_R \Omega) \simeq \mathrm{Fin}(\deg i)$. Write $X = C \times_{\operatorname{Spec} R} \operatorname{Spec} \Omega$, $U_\Omega$ for the preimage of $U$ in $X$, and $\varepsilon_\Omega$ for the closed point of the $\Omega$-section of $X$ induced by $\varepsilon$. Let $c_1 : C_1 \to \operatorname{Spec}\Omega$, $c_2 : C_2 \to \operatorname{Spec}\Omega$ be proper, smooth of relative dimension $1$ and geometrically integral, with closed immersions $i_1, i_2$ into $X$ over $\operatorname{Spec}\Omega$, and assume: $X$ is set-theoretically the union of the images of $i_1$ and $i_2$; $C_1 \times_X C_2$ is reduced with exactly $n > 0$ points, $n > 0$; $\varepsilon_\Omega$ lies in the image of $i_1$ but not of $i_2$; $U_\Omega$ is the complement of the image of $C_1 \times_X C_2$ in $X$; the image of $i_1$ meets $U_\Omega$ exactly in the connected component of $\varepsilon_\Omega$ in $U_\Omega$, and the image of $i_2$ meets $U_\Omega$ exactly in the rest of $U_\Omega$; and there are opens $W_1, W_2$ of $X$ with underlying sets the complements of the images of $i_2$, resp. $i_1$, such that $i_\nu^{-1}W_\nu \hookrightarrow C_\nu \to X$ is an open immersion. Assume further that each $\operatorname{Spec} B_i$ pulls back into that connected component of $\varepsilon_\Omega$. Let $r, \gamma_1, e_1$ be naturals and $\mathcal V_1$ a two-affine open cover of $C_1$ (two affine opens with affine intersection covering $C_1$) with $\dim_\Omega$ of the Čech $H^1$ of the structure sheaf on $\mathcal V_1$ equal to $\gamma_1$, subject to $\gamma_1 + n + e_1 = r+1$, $2\gamma_1 + n \le r+1$ and $r b^{e_1} + e_1 < M$. Finally let $r'$ be a natural number, $q_1,\dots,q_d$ be $\Omega$-sections of $X$ with images in $U_\Omega$ off the image of $i_1$, and $L_0$ an invertible module on $X$ satisfying `IsAlgEquivZero` for $X \to \operatorname{Spec}\Omega$, i.e. $L_0$ is the fibre at one section of an invertible module on $X \times_{\operatorname{Spec}\Omega} T$ for some geometrically integral $T$ of locally finite type whose fibre at another section is trivial. Then there exists an injective $a : \mathrm{Fin}\,e_1 \to \mathrm{Fin}\,M$ such that for every family $v$ of $e_1$ $\Omega$-sections of $X$ with $v_j$ lying over $z_{a(j)}$ via some $R$-algebra map $B_{a(j)} \to \Omega$, every further finite family $v'$ of $\Omega$-sections of $X$ with images in $U_\Omega$ off the image of $i_1$, and every two-affine open cover $\mathcal W_1$ of $C_1$, the Čech $H^0$ of the sections on $\mathcal W_1$ of $i_1^*\bigl(L_0 \otimes (\mathcal I_{\varepsilon_\Omega}^{\,r}\,(\prod_m \mathcal I_{q_m})^{r'})^{\vee} \otimes \prod_j \mathcal I_{v_j}\prod_j \mathcal I_{v'_j}\bigr) \otimes \mathcal I_{C_1\times_X C_2 \subset C_1}$ has $\Omega$-dimension $0$, and its Čech $H^1$ is a subsingleton; here $\mathcal I_\bullet$ denotes the ideal-sheaf module of the kernel ideal of the indicated morphism, and $(\cdot)^{\vee}$ its dual.
--
--   This is the near-side (i.e. $\varepsilon$-component) half of a general-position statement at a geometric fibre that degenerates into two smooth proper geometrically integral curves meeting transversally in $n$ points: it produces $e_1$ of the $M$ given disjoint blocks whose $\Omega$-points, however chosen inside the selected blocks, make the twisted sheaf on the $\varepsilon$-component acyclic in the two-chart Čech sense. It feeds the two-sided blocks statement [`AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration`](thm.html#AlgebraicGeometry.RelPicard.exists_split_injective_forall_subsingleton_H1_and_support_subset_of_twoSidedBlocks_of_twoGluedSmoothCurveDegeneration).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration.lean

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

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) {b : ℕ} (hb : 1 ≤ b) (hdegb : ∀ i, deg i ≤ b)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i))

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

    (hzε : ∀ i, (pullback.fst c (SmoothProperCurve.specMap R Ω)).base ⁻¹' Set.range (z i).base ⊆
      connectedComponentIn (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω)))
        (((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1).base (IsLocalRing.closedPoint Ω)))

    (r γ₁ e₁ : ℕ) (𝒱₁ : C₁.TwoAffineOpenCover)
    (hγ₁ : Module.finrank Ω (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf)).H1 = γ₁)
    (he₁ : γ₁ + n + e₁ = r + 1) (hr₁ : 2 * γ₁ + n ≤ r + 1)
    (hcount₁ : r * b ^ e₁ + e₁ < M)

    (r' : ℕ) {d : ℕ} (q : Fin d → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
    (hq₁ : ∀ m, Set.range (q m).1.base ⊆
      (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₁.1.base)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a : Fin e₁ → Fin M, Function.Injective a ∧
      ∀ (v : Fin e₁ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        ∀ {e₂ : ℕ} (v' : Fin e₂ → {p : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          p ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _}),
          (∀ j, Set.range (v' j).1.base ⊆
            (((pullback.fst c (SmoothProperCurve.specMap R Ω)) ⁻¹ᵁ U : (pullback c (SmoothProperCurve.specMap R Ω)).Opens) : Set ↥(pullback c (SmoothProperCurve.specMap R Ω))) \ Set.range i₁.1.base) →
          ∀ 𝒲₁ : C₁.TwoAffineOpenCover,
            Module.finrank Ω (𝒲₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗
                ((pullback.fst i₁.1 i₂.1).ker).module)).H0 = 0 ∧
            Subsingleton (𝒲₁.sectionsOf c₁ ((Scheme.Modules.pullback i₁.1).obj
              (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
              ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗
                ((pullback.fst i₁.1 i₂.1).ker).module)).H1 := by sorry
