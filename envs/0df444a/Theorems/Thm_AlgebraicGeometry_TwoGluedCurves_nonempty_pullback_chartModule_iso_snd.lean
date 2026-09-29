-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd
-- name    : AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_iso_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/6c2fbb07-2f18-57c1-be51-eb246032b684
-- title:
--   Restriction of the two-sided chart bundle to the second component
-- statement:
--   Let $k$ be a field, $x : X \to \operatorname{Spec} k$ a scheme over $k$, and $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ two further $k$-schemes, together with $k$-morphisms $i_1 : C_1 \to X$ and $i_2 : C_2 \to X$ (elements of `SchemeHomOver`, i.e. satisfying $x \circ i_\nu = c_\nu$) whose underlying scheme morphisms are closed immersions. Assume given an open $W_2 \subseteq X$ whose underlying set is the complement of the image of $i_1$, and assume that the inclusion of the open subscheme $i_2^{-1}W_2 \subseteq C_2$ followed by $i_2$ is an open immersion. Let $L_0$ be a module on $X$ that is invertible in the sense of `Scheme.Modules.IsInvertible` (every point has an open neighbourhood $U$ on which the pullback of $L_0$ along $U.\iota$ is isomorphic to the unit module). Let $r, r' \in \mathbb{N}$. Let $\varepsilon_0$ and $v_j$ ($j \in \operatorname{Fin} e_1$) be sections of $x$ (morphisms $\operatorname{Spec} k \to X$ splitting $x$) whose images avoid the image of $i_2$ and whose kernel ideal sheaves are invertible in the sense of `IsInvertible` (locally generated on an affine basic open by a single non-zero-divisor). Let $q_m$ ($m \in \operatorname{Fin} d$) and $v'_j$ ($j \in \operatorname{Fin} e_2$) be sections of $x$ whose images avoid the image of $i_1$, again with invertible kernel ideal sheaves, and equipped with lifts $q_{2,m}$, $v_{2,j}$ to sections of $c_2$ satisfying $i_2 \circ q_{2,m} = q_m$ and $i_2 \circ v_{2,j} = v'_j$. The conclusion asserts that the following two modules on $C_2$ admit an isomorphism (the statement is the nonemptiness of the type of such isomorphisms): the pullback along $i_2$ of $$L_0 \otimes \bigl(\bigl(\ker(\varepsilon_0)^r \cdot (\textstyle\prod_m \ker(q_m))^{r'}\bigr)^{\vee} \otimes \bigl((\textstyle\prod_j \ker(v_j))(\textstyle\prod_j \ker(v'_j))\bigr)\bigr),$$ and $$(i_2^* L_0) \otimes \bigl(\bigl(\textstyle\prod_{(m,l) \in \operatorname{Fin} d \times \operatorname{Fin} r'} \ker(q_{2,m})\bigr)^{\vee} \otimes \textstyle\prod_j \ker(v_{2,j})\bigr),$$ where for an ideal sheaf $I$ the module $I.\mathrm{module}$ is the kernel of the map from the unit module to the pushforward of the unit module along the closed immersion of the associated subscheme, and $I.\mathrm{invModule}$ is its dual. Thus on $C_2$ the contributions of $\varepsilon_0$ and of the $v_j$ disappear, while each $q_m$ occurs with multiplicity $r'$ through its lift and each $v'_j$ through its lift.
--
--   This is the dictionary entry computing the restriction to the second component $C_2$ of a line bundle on $X$ written in chart form, i.e. as $L_0$ twisted by divisors supported at a prescribed finite set of $k$-rational sections: points lying off $C_2$ restrict trivially, while points lying off $C_1$ restrict to their chosen lifts because $i_2$ is an open immersion there. It feeds the analysis of restriction maps on the relative Picard functor for a fibre that is a union of two smooth curves, used in [`AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration`](thm.html#AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_iso_snd.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_iso_snd
    (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (W₂ : X.Opens) (hW₂ : (W₂ : Set X) = (Set.range i₁.1.base)ᶜ) (hoi : IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1))
    (L₀ : X.Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)

    (r : ℕ) (ε₀ : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hε₀ : Set.range ε₀.1.base ⊆ (Set.range i₂.1.base)ᶜ) (hε₀i : ε₀.1.ker.IsInvertible)
    {e₁ : ℕ} (v : Fin e₁ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv : ∀ j, Set.range (v j).1.base ⊆ (Set.range i₂.1.base)ᶜ)
    (hvi : ∀ j, (v j).1.ker.IsInvertible)

    (r' : ℕ) {d : ℕ} (q : Fin d → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hq : ∀ m, Set.range (q m).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hqi : ∀ m, (q m).1.ker.IsInvertible) (q₂ : Fin d → {p : Spec (CommRingCat.of k) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) (hq₂ : ∀ m, (q₂ m).1 ≫ i₂.1 = (q m).1)
    {e₂ : ℕ} (v' : Fin e₂ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv' : ∀ j, Set.range (v' j).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hv'i : ∀ j, (v' j).1.ker.IsInvertible) (v₂ : Fin e₂ → {p : Spec (CommRingCat.of k) ⟶ C₂ // p ≫ c₂ = 𝟙 _}) (hv₂ : ∀ j, (v₂ j).1 ≫ i₂.1 = (v' j).1) :
    Nonempty (
      (Scheme.Modules.pullback i₂.1).obj
          (L₀ ⊗ (((ε₀.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ≅
      (Scheme.Modules.pullback i₂.1).obj L₀ ⊗
        ((∏ ml : Fin d × Fin r', (q₂ ml.1).1.ker).invModule ⊗ (∏ j, (v₂ j).1.ker).module)) := by sorry
