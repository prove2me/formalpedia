-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced
-- name    : AlgebraicGeometry.IsClosedImmersion.app_curveChange_injective_and_exists_of_app_eq_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/1f90b808-d44c-5029-9be9-2dcfd915d4ef
-- title:
--   Mayer–Vietoris for a closed cover, after base change
-- statement:
--   Let $k$ be a field and let $X,Y_1,Y_2,Z$ be schemes equipped with morphisms $x\colon X\to\operatorname{Spec}k$, $y_1\colon Y_1\to\operatorname{Spec}k$, $y_2\colon Y_2\to\operatorname{Spec}k$, $z\colon Z\to\operatorname{Spec}k$, with $X$ reduced. Suppose given morphisms over $\operatorname{Spec}k$, that is $i_1\colon Y_1\to X$ with $i_1$ followed by $x$ equal to $y_1$ and $i_2\colon Y_2\to X$ with $i_2$ followed by $x$ equal to $y_2$, both $i_1$ and $i_2$ closed immersions, such that every point of $X$ lies in the image of $i_1$ or in the image of $i_2$; and morphisms $j_1\colon Z\to Y_1$, $j_2\colon Z\to Y_2$ over $\operatorname{Spec}k$ exhibiting $Z$ as the fibre product of $i_1$ and $i_2$ (the square with sides $j_1,j_2,i_1,i_2$ is a pullback square). Let $t\colon T\to\operatorname{Spec}k$ be any $k$-scheme, and write $(-)_T$ for the base-changed morphism obtained from a morphism over $\operatorname{Spec}k$ by taking fibre products with $t$ (`curveChange`, the map induced on pullbacks by the given morphism and the identity of $T$). Assume that $(j_1)_T$ followed by $(i_1)_T$ equals $(j_2)_T$ followed by $(i_2)_T$ as morphisms $Z\times_k T\to X\times_k T$. Then for every open subset $U$ of $X\times_k T$: (i) the map sending $f\in\Gamma(U,\mathcal O_{X\times_k T})$ to the pair of its pullbacks under $(i_1)_T$ and $(i_2)_T$ is injective; and (ii) for all sections $g_1\in\Gamma((i_1)_T^{-1}U,\mathcal O_{Y_1\times_k T})$ and $g_2\in\Gamma((i_2)_T^{-1}U,\mathcal O_{Y_2\times_k T})$ whose pullbacks to $Z\times_k T$ agree — the pullback of $g_1$ along $(j_1)_T$ being compared with that of $g_2$ along $(j_2)_T$ after transport along the equality $(j_2)_T^{-1}(i_2)_T^{-1}U=(j_1)_T^{-1}(i_1)_T^{-1}U$ coming from the assumed commutativity — there exists $f\in\Gamma(U,\mathcal O_{X\times_k T})$ pulling back to $g_1$ under $(i_1)_T$ and to $g_2$ under $(i_2)_T$.
--
--   This is the Mayer–Vietoris, or gluing, property of functions on a scheme covered by two closed subschemes, asserted after an arbitrary base change $T\to\operatorname{Spec}k$ (so that $X\times_k T$ itself need not be reduced): sections on $U$ are exactly pairs of sections on the two closed pieces that agree on their intersection. It is used in the construction of invertible modules on base changes of a curve from data on a closed cover, via [`AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_curveChange_iso_of_closedCover).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.IsClosedImmersion.app_curveChange_injective_and_exists_of_app_eq_of_isReduced
    {k : Type u} [Field k] {X Y₁ Y₂ Z : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base)
    (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂) (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t)
    (U : (Limits.pullback x t).Opens) :
    Function.Injective (fun f : Γ(Limits.pullback x t, U) =>
      ((curveChange i₁.1 i₁.2 t).app U f, (curveChange i₂.1 i₂.2 t).app U f)) ∧
      ∀ (g₁ : Γ(Limits.pullback y₁ t, (curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U))
        (g₂ : Γ(Limits.pullback y₂ t, (curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U)),
        (Limits.pullback z t).presheaf.map
            (eqToHom (show (curveChange j₂.1 j₂.2 t) ⁻¹ᵁ ((curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U) =
                (curveChange j₁.1 j₁.2 t) ⁻¹ᵁ ((curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
          ((curveChange j₁.1 j₁.2 t).app ((curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U) g₁) =
          (curveChange j₂.1 j₂.2 t).app ((curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(Limits.pullback x t, U),
          (curveChange i₁.1 i₁.2 t).app U f = g₁ ∧ (curveChange i₂.1 i₂.2 t).app U f = g₂ := by sorry
