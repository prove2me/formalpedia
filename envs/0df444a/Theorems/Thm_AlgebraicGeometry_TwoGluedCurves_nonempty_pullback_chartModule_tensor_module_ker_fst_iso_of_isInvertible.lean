-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible
-- name    : AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/ddcabc12-c66b-562f-a62a-08b23ce465c7
-- title:
--   Chart module restricted along i₁ and twisted by crossings
-- statement:
--   Let $k$ be a field and let $x : X \to \operatorname{Spec} k$, $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be schemes over $k$, and let $i_1, i_2$ be $k$-morphisms $C_1 \to X$, $C_2 \to X$ (each given as a morphism together with the identity $i_j \circ \ldots$ expressing compatibility with the structure maps) whose underlying morphisms are closed immersions. Let $W_1$ be an open subscheme of $X$ whose underlying set is the complement of the image of $i_2$, and assume that the inclusion of $i_1^{-1}W_1$ into $C_1$ followed by $i_1$ is an open immersion. Let $L_0$ be a module on $X$ which is invertible in the sense that every point has an open neighbourhood $U$ for which the pullback of $L_0$ along $U \hookrightarrow X$ is isomorphic to the unit module. Fix $r, r' \in \mathbb{N}$. Let $\varepsilon_0$ be a $k$-point of $X$ (a section of $x$) whose image avoids the image of $i_2$ and whose kernel ideal sheaf is invertible, in the sense that around each point of $X$ there are an affine open $U$, a section $f$ on $U$ and a nonzerodivisor $g$ on the affine basic open of $f$ generating the ideal there; let $\varepsilon_1$ be a $k$-point of $C_1$ with $i_1 \circ \varepsilon_1 = \varepsilon_0$. Let $v_j$, $j \in \mathrm{Fin}\,e_1$, be $k$-points of $X$ avoiding the image of $i_2$, with invertible kernel ideals and with lifts $v_{1,j}$ to $C_1$ along $i_1$; let $q_m$, $m \in \mathrm{Fin}\,d$, and $v'_j$, $j \in \mathrm{Fin}\,e_2$, be $k$-points of $X$ avoiding the image of $i_1$, all with invertible kernel ideals. Assume finally that the kernel ideal sheaf $I_N$ of the projection $\mathrm{pullback.fst}\,i_1\,i_2 : C_1 \times_X C_2 \to C_1$ is invertible. Then there exists an isomorphism of modules on $C_1$ between the pullback along $i_1$ of $L_0 \otimes \bigl(\bigl(I_{\varepsilon_0}^{\,r}\cdot(\prod_m I_{q_m})^{r'}\bigr)^{\vee} \otimes \bigl((\prod_j I_{v_j})\cdot(\prod_j I_{v'_j})\bigr)\bigr)$, tensored with the module of $I_N$, and $i_1^{*}L_0 \otimes \bigl((\prod_{l \in \mathrm{Fin}\,r} I_{\varepsilon_1})^{\vee} \otimes \bigl((\prod_j I_{v_{1,j}})\cdot I_N\bigr)\bigr)$, where for an ideal sheaf $I$ the module of $I$ is the kernel of the unit-to-pushforward-of-unit map of the closed immersion of the corresponding subscheme, and $I^{\vee}$ denotes its dual in the monoidal category of modules.
--
--   This is the dictionary step that transfers a line bundle with prescribed positive and negative twists on the ambient scheme $X$ to the component $C_1$ of a two-component configuration, converting the twist by the crossing ideal $I_N$ of $C_1 \times_X C_2 \to C_1$ into the shape required on $C_1$: the positive part becomes the $r$-fold product of the ideal of the lifted point $\varepsilon_1$, and the negative part becomes the product of the ideals of the lifted points $v_{1,j}$ times $I_N$. It is used in the construction of sections with prescribed cohomological behaviour for two glued smooth curves, namely in [`AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration`](thm.html#AlgebraicGeometry.RelPicard.exists_injective_forall_finrank_H0_eq_zero_and_subsingleton_H1_restrict_fst_of_nearBlocks_of_twoGluedSmoothCurveDegeneration).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible.lean

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

theorem AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible
    (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (W₁ : X.Opens) (hW₁ : (W₁ : Set X) = (Set.range i₂.1.base)ᶜ) (hoi : IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1))
    (L₀ : X.Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)

    (r : ℕ) (ε₀ : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hε₀ : Set.range ε₀.1.base ⊆ (Set.range i₂.1.base)ᶜ)
    (hε₀i : ε₀.1.ker.IsInvertible) (ε₁ : {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _}) (hε₁ : ε₁.1 ≫ i₁.1 = ε₀.1)
    {e₁ : ℕ} (v : Fin e₁ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv : ∀ j, Set.range (v j).1.base ⊆ (Set.range i₂.1.base)ᶜ)
    (hvi : ∀ j, (v j).1.ker.IsInvertible) (v₁ : Fin e₁ → {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _}) (hv₁ : ∀ j, (v₁ j).1 ≫ i₁.1 = (v j).1)

    (r' : ℕ) {d : ℕ} (q : Fin d → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hq : ∀ m, Set.range (q m).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hqi : ∀ m, (q m).1.ker.IsInvertible)
    {e₂ : ℕ} (v' : Fin e₂ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv' : ∀ j, Set.range (v' j).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hv'i : ∀ j, (v' j).1.ker.IsInvertible)

    (hK : ((pullback.fst i₁.1 i₂.1).ker).IsInvertible) :
    Nonempty (
      (Scheme.Modules.pullback i₁.1).obj
          (L₀ ⊗ (((ε₀.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗
        ((pullback.fst i₁.1 i₂.1).ker).module ≅
      (Scheme.Modules.pullback i₁.1).obj L₀ ⊗
        ((∏ _l : Fin r, ε₁.1.ker).invModule ⊗ ((∏ j, (v₁ j).1.ker) * (pullback.fst i₁.1 i₂.1).ker).module)) := by sorry
