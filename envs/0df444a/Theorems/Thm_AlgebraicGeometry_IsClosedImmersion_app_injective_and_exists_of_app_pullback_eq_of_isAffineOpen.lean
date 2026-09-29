-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
-- name    : AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/76d7b830-8026-52ba-955c-ede90119f820
-- title:
--   Affine Mayer–Vietoris for two closed subschemes covering a reduced scheme
-- statement:
--   Let $X$, $Y_1$, $Y_2$ be schemes, with $X$ reduced, and let $i_1 : Y_1 \to X$ and $i_2 : Y_2 \to X$ be closed immersions whose images cover $X$, i.e. the union of the ranges of the underlying continuous maps of $i_1$ and $i_2$ is all of $X$. Let $U$ be an open subset of $X$ which is an affine open. Then two things hold. First, the ring map $\Gamma(X, U) \to \Gamma(Y_1, i_1^{-1}U) \times \Gamma(Y_2, i_2^{-1}U)$, $f \mapsto (i_1^\sharp(f), i_2^\sharp(f))$, given by the two comparison maps on sections over $U$, is injective. Second, for all sections $g_1 \in \Gamma(Y_1, i_1^{-1}U)$ and $g_2 \in \Gamma(Y_2, i_2^{-1}U)$ whose pull-backs to the fibre product $Y_1 \times_X Y_2$ agree — precisely: the image of $g_1$ under the map of sections attached to $\mathrm{pr}_1$ over $i_1^{-1}U$, transported along the equality of opens $\mathrm{pr}_2^{-1}(i_2^{-1}U) = \mathrm{pr}_1^{-1}(i_1^{-1}U)$ coming from $\mathrm{pr}_1 \circ i_1 = \mathrm{pr}_2 \circ i_2$, equals the image of $g_2$ under the map attached to $\mathrm{pr}_2$ over $i_2^{-1}U$ — there exists $f \in \Gamma(X, U)$ with $i_1^\sharp(f) = g_1$ and $i_2^\sharp(f) = g_2$. The converse implication, that sections coming from $\Gamma(X,U)$ are always compatible on the fibre product, is not part of the conclusion.
--
--   This is the affine-open case of the Mayer–Vietoris (pushout) description of a reduced scheme covered by two closed subschemes: over an affine open, sections of $\mathcal{O}_X$ are exactly the pairs of sections of $\mathcal{O}_{Y_1}$ and $\mathcal{O}_{Y_2}$ agreeing on the scheme-theoretic intersection $Y_1 \times_X Y_2$. It is used to obtain the corresponding statement without the affineness hypothesis on $U$, and in the construction of rings of functions on two projective lines glued along a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by sorry
