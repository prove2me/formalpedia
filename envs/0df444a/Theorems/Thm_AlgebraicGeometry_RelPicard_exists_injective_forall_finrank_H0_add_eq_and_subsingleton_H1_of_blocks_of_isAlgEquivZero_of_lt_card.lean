-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3ed99213-e281-52df-8663-563a403e27c9
-- title:
--   Block general position: prescribed h⁰ and vanishing Čech H¹
-- statement:
--   Let $K$ be an algebraically closed field, and let $x : X \to \operatorname{Spec} K$ be a morphism with $X$ integral, $x$ proper and smooth of relative dimension $1$. Fix $\gamma \in \mathbb{N}$ and a two-affine open cover $\mathcal{V}_0$ of $X$ (two affine opens with affine intersection whose union is $X$) such that the first two-chart Čech cohomology of the structure sheaf — the quotient of the sections over $\mathcal{V}_0.U_0 \cap \mathcal{V}_0.U_1$ by the image of the Čech differential — has $K$-dimension $\gamma$. Let $L$ be a module on $X$ that is invertible (locally isomorphic to the unit module) and satisfies `IsAlgEquivZero x L`: there are a locally of finite type, geometrically integral $h : T' \to \operatorname{Spec} K$, an invertible module $M$ on $X \times_K T'$ and two sections $t_0, t_1$ of $h$ whose base-changed pullbacks of $M$ are isomorphic to the unit module and to the pullback of $L$ respectively. Points below are $K$-points of $X$, i.e. morphisms $q : \operatorname{Spec} K \to X$ with $q \circ x$ (in diagrammatic order, $q$ followed by $x$) the identity. Given $w : \mathrm{Fin}\,t \to$ such points, finite sets $S_\kappa$ of such points for $\kappa \in \mathrm{Fin}\,N$, and $e \in \mathbb{N}$ with $2\gamma + \#S_\kappa \le t+1$ and $e + \#S_\kappa + \gamma \le t+1$ for all $\kappa$; given a finite type $\iota$ with decidable equality and pairwise disjoint finite sets $B_i$ of such points with $1 \le b$, $\#B_i \le b$ for all $i$, and $N t b^{e} + e < \#\iota$; then there is an injective $a : \mathrm{Fin}\,e \to \iota$ such that for every transversal $v$ with $v_j \in B_{a_j}$, every $\kappa$ and every two-affine open cover $\mathcal{V}$ of $X$, the module $L \otimes \big(\big(\prod_l \ker w_l\big)^{\vee\text{-module}} \otimes \big(\big(\prod_j \ker v_j\big)\cdot\prod_{p \in S_\kappa} \ker p\big)\text{-module}\big)$ — where for an ideal sheaf $I$ the associated module is the kernel of the unit module mapping to the pushforward of the unit along the closed subscheme inclusion, and `invModule` is its dual, so that this is $L \otimes \mathcal{O}(\sum_l w_l - \sum_j v_j - \sum_{p\in S_\kappa} p)$ — has Čech $H^0$ (the kernel of the Čech differential on the two charts) of $K$-dimension satisfying $h^0 + e + \#S_\kappa + \gamma = t+1$, and Čech $H^1$ a subsingleton.
--
--   This is a Riemann–Roch general position statement in Čech form: from a budget condition $\#\iota > N t b^{e} + e$ on a family of disjoint blocks of $K$-points it extracts $e$ blocks all of whose transversals impose independent conditions, simultaneously for the $N$ prescribed auxiliary sets $S_\kappa$, giving the exact value of $h^0$ and the vanishing of $H^1$ on any two-affine cover. It is used in the construction of charts for relative Picard functors, being cited by the statements on near and far blocks for two-glued smooth curve degenerations and by the two-sided block statement with prescribed support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_add_eq_and_subsingleton_H1_of_blocks_of_isAlgEquivZero_of_lt_card
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (γ : ℕ) (𝒱₀ : X.TwoAffineOpenCover)
    (hγ : Module.finrank K (𝒱₀.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H1 = γ)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)

    {t : ℕ} (w : Fin t → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})

    {N : ℕ} (S : Fin N → Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) (e : ℕ)
    (hS : ∀ κ, 2 * γ + (S κ).card ≤ t + 1) (heS : ∀ κ, e + (S κ).card + γ ≤ t + 1)

    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * t * b ^ e + e < Fintype.card ι) :
    ∃ a : Fin e → ι, Function.Injective a ∧
      ∀ v : Fin e → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}, (∀ j, v j ∈ B (a j)) →
        ∀ κ, ∀ 𝒱 : X.TwoAffineOpenCover,
          Module.finrank K (𝒱.sectionsOf x
              (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H0
            + e + (S κ).card + γ = t + 1 ∧
          Subsingleton (𝒱.sectionsOf x
              (L ⊗ ((∏ l, (w l).1.ker).invModule ⊗ ((∏ j, (v j).1.ker) * ∏ p ∈ S κ, p.1.ker).module))).H1 := by sorry
