-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_iso_of_milnorSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/f1cab52c-565c-55ad-bdef-e3a29ec0f1cb
-- title:
--   Milnor patching of invertible modules along a square of closed immersions
-- statement:
--   Let $W, V_1, V_2, Z$ be schemes and let $i_1\colon V_1\to W$, $i_2\colon V_2\to W$, $j_1\colon Z\to V_1$, $j_2\colon Z\to V_2$ be morphisms with $i_1$, $i_2$ and $j_2$ closed immersions, satisfying $j_1$ followed by $i_1$ equal to $j_2$ followed by $i_2$. Assume the Milnor condition on functions: for every open $U\subseteq W$ the map $f\mapsto (i_1^\sharp f, i_2^\sharp f)$ from $\Gamma(W,U)$ to $\Gamma(V_1, i_1^{-1}U)\times\Gamma(V_2,i_2^{-1}U)$ is injective, and for every pair $(g_1,g_2)$ whose pullbacks to $\Gamma(Z, j_1^{-1}i_1^{-1}U) = \Gamma(Z, j_2^{-1}i_2^{-1}U)$ (identified via the equality of the two composites) agree, there is $f\in\Gamma(W,U)$ with $i_1^\sharp f = g_1$ and $i_2^\sharp f = g_2$. Let $L_1$ be a module on $V_1$ and $L_2$ a module on $V_2$, each invertible in the sense that every point of the base has an open neighbourhood $U$ over which the pullback along $U\hookrightarrow$ base is isomorphic to the unit module of the ring sheaf of $U$, and let $\varphi\colon j_1^{*}L_1\cong j_2^{*}L_2$ be an isomorphism. Then there exist an invertible module $L$ on $W$ and isomorphisms $\alpha_1\colon i_1^{*}L\cong L_1$, $\alpha_2\colon i_2^{*}L\cong L_2$ such that $j_1^{*}\alpha_1$ followed by $\varphi$ equals the canonical identification $j_1^{*}i_1^{*}L\cong j_2^{*}i_2^{*}L$ (built from the pullback-composition isomorphisms and the congruence isomorphism attached to the commutativity of the square) followed by $j_2^{*}\alpha_2$.
--
--   This is Milnor patching of invertible modules over a square of closed subschemes, in sheaf-theoretic form: the sections condition replaces the cartesian square of rings with one surjective side. It is the base-change-free core used to glue line bundles along a two-piece closed cover, and is invoked in the construction of invertible modules on curves obtained from such covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_iso_of_milnorSquare
    {W V₁ V₂ Z : Scheme.{u}} (i₁ : V₁ ⟶ W) (i₂ : V₂ ⟶ W) (j₁ : Z ⟶ V₁) (j₂ : Z ⟶ V₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion j₂] (hsq : j₁ ≫ i₁ = j₂ ≫ i₂)
    (hmil : ∀ U : W.Opens,
      Function.Injective (fun f : Γ(W, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
        ∀ (g₁ : Γ(V₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(V₂, i₂ ⁻¹ᵁ U)),
          Z.presheaf.map
              (eqToHom (show j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
            ((j₁.app (i₁ ⁻¹ᵁ U)) g₁) = (j₂.app (i₂ ⁻¹ᵁ U)) g₂ →
          ∃ f : Γ(W, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂)
    (L₁ : V₁.Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (L₂ : V₂.Modules) (hL₂ : Scheme.Modules.IsInvertible L₂)
    (φ : (Scheme.Modules.pullback j₁).obj L₁ ≅ (Scheme.Modules.pullback j₂).obj L₂) :
    ∃ (L : W.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (α₁ : (Scheme.Modules.pullback i₁).obj L ≅ L₁) (α₂ : (Scheme.Modules.pullback i₂).obj L ≅ L₂),
        (Scheme.Modules.pullback j₁).map α₁.hom ≫ φ.hom =
          ((Scheme.Modules.pullbackComp j₁ i₁).app L).hom ≫ ((Scheme.Modules.pullbackCongr hsq).app L).hom ≫
            ((Scheme.Modules.pullbackComp j₂ i₂).app L).inv ≫ (Scheme.Modules.pullback j₂).map α₂.hom := by sorry
