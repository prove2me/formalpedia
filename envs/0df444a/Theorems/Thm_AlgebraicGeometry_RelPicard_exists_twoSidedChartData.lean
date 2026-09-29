-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoSidedChartData
-- name    : AlgebraicGeometry.RelPicard.exists_twoSidedChartData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d0b9afe9-9f40-528b-b9e6-1b33226d2d6d
-- title:
--   Two-sided chart data: sections and chart divisors on C_A
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a separated morphism of schemes and $U\subseteq C$ an open subscheme such that the composite of the inclusion $U\hookrightarrow C$ with $c$ is smooth of relative dimension $1$. Let $A$ be a nontrivial $R$-algebra, let $M,M'$ be naturals, and let $B_i$ ($i<M$) and $B'_i$ ($i<M'$) be $R$-algebras together with degrees $\deg i$, $\deg' i$ and $A$-algebra isomorphisms $A\otimes_R B_i\cong A^{\deg i}$ and $A\otimes_R B'_i\cong A^{\deg' i}$. Assume given closed immersions $z_i\colon\operatorname{Spec}B_i\to C$ and $z'_i\colon\operatorname{Spec}B'_i\to C$ that are compatible with the structure morphisms, i.e. $z_i$ followed by $c$ is $\operatorname{Spec}$ of the structure map $R\to B_i$ (likewise for $z'_i$), and whose topological images lie in $U$. Let $e$ be a natural number. Then there exist families $\sigma_i\colon \mathrm{Fin}(\deg i)\to\{\varphi\colon\operatorname{Spec}A\to C\times_{\operatorname{Spec}R}\operatorname{Spec}A \mid \varphi\text{ a section of }\mathrm{baseChange}\ R\ c\ A\}$ and $\sigma'_i$ on $\mathrm{Fin}(\deg' i)$, each injective, such that for all $i,m$ the morphism $\sigma_i(m)$ followed by the first projection $C\times_{\operatorname{Spec}R}\operatorname{Spec}A\to C$ factors as some $y\colon\operatorname{Spec}A\to\operatorname{Spec}B_i$ followed by $z_i$ (likewise for $\sigma'$ and $z'$); a finite type $\iota$ in the same universe; an indexing map $\mathrm{idx}$ assigning to each splitting $e_1+e_2=e$, each injective $a\colon\mathrm{Fin}(e_1)\to\mathrm{Fin}(M)$, each injective $a'\colon\mathrm{Fin}(e_2)\to\mathrm{Fin}(M')$ and each pair of choice functions $m\colon\prod_i\mathrm{Fin}(\deg i)$, $m'\colon\prod_i\mathrm{Fin}(\deg' i)$ an element of $\iota$; and a family $D_\gamma$ indexed by $\iota$ of data consisting of an ideal sheaf on the pullback of $\mathrm{baseChange}\ R\ c\ A$ along the identity of $\operatorname{Spec}A$ whose associated closed subscheme is finite, flat and locally of finite presentation over $\operatorname{Spec}A$ with fibrewise rank $e$ at every point; these satisfy, for every such tuple, that the ideal of $D_\gamma(\mathrm{idx}\,e_1\,e_2\,\cdots)$ is the product of the product over $j<e_1$ of the kernel ideals of the graphs of the sections $\sigma_{a(j)}(m(a(j)))$ with the product over $j<e_2$ of the kernel ideals of the graphs of the $\sigma'_{a'(j)}(m'(a'(j)))$, and that for every index the support of the ideal of $D_\gamma$ is contained in the preimage of the preimage of $U$ under the first projection.
--
--   This is the packaging step of the two-sided chart system for the relative Picard functor of a curve degenerating into two components: it simultaneously produces the $A$-sections of the base-changed curve cut out by the two pools of split blocks, a finite index set for the chart data (splittings of $e$ together with injective transversals into the two pools and choices of sections), and the corresponding relative effective Cartier divisors of degree $e$ supported in the smooth locus. It is used in the construction of the representing charts for the relative $\operatorname{Pic}$ in [`AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.forall_prime_exists_representsRelSubPic_algEquivZeroCut_baseChange_away_of_smoothLocus_of_twoGluedSmoothCurveDegenerations), and rests on the existence of sections splitting a block over $A$, on the realisation of a sum of sections as a relative effective divisor, and on the closure of divisors supported in the smooth locus under products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoSidedChartData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelPicard.exists_twoSidedChartData
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A]
    {M M' : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (B' : Fin M' → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra R (B' i)]
    (deg : Fin M → ℕ) (φ : ∀ i, TensorProduct R A (B i) ≃ₐ[A] (Fin (deg i) → A))
    (deg' : Fin M' → ℕ) (φ' : ∀ i, TensorProduct R A (B' i) ≃ₐ[A] (Fin (deg' i) → A))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C) [∀ i, IsClosedImmersion (z i)]
    (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ C) [∀ i, IsClosedImmersion (z' i)]
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hz' : ∀ i, z' i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B' i))))
    (hzU : ∀ i, Set.range (z i).base ⊆ (U : Set C)) (hz'U : ∀ i, Set.range (z' i).base ⊆ (U : Set C))
    (e : ℕ) :
    ∃ (σ : ∀ i, Fin (deg i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
      (σ' : ∀ i, Fin (deg' i) → SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (baseChange R c A))
      (_ : ∀ i, Function.Injective (σ i)) (_ : ∀ i, Function.Injective (σ' i))
      (_ : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B i)),
        (σ i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z i)
      (_ : ∀ i m, ∃ y : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (B' i)),
        (σ' i m).1 ≫ pullback.fst c (specMap R A) = y ≫ z' i)
      (ι : Type u) (_ : Finite ι)
      (idx : ∀ (e₁ e₂ : ℕ), e₁ + e₂ = e → {a : Fin e₁ → Fin M // Function.Injective a} →
        {a' : Fin e₂ → Fin M' // Function.Injective a'} → (∀ i, Fin (deg i)) → (∀ i, Fin (deg' i)) → ι)
      (Dγ : ι → RelEffCartierDiv (baseChange R c A) e (𝟙 (Spec (CommRingCat.of A)))),
      (∀ (e₁ e₂ : ℕ) (he : e₁ + e₂ = e) (a : {a : Fin e₁ → Fin M // Function.Injective a})
        (a' : {a' : Fin e₂ → Fin M' // Function.Injective a'}) (m : ∀ i, Fin (deg i)) (m' : ∀ i, Fin (deg' i)),
        (Dγ (idx e₁ e₂ he a a' m m')).I =
          prodKerGraph (baseChange R c A) (fun j => (σ (a.1 j) (m (a.1 j))).1) (fun j => (σ (a.1 j) (m (a.1 j))).2) *
          prodKerGraph (baseChange R c A) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).1) (fun j => (σ' (a'.1 j) (m' (a'.1 j))).2)) ∧
      (∀ i, (Dγ i).SupportedIn (pullback.fst c (specMap R A) ⁻¹ᵁ U)) := by sorry
