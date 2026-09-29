-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback
-- name    : AlgebraicGeometry.isPullback_pullback_lift_morphismRestrict_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/97b9f055-ced1-52a4-9866-18f7a154c937
-- title:
--   Cartesianness of the product chart over Specπ
-- statement:
--   Let $\pi \colon T' \to T$ be a homomorphism of commutative rings, let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a morphism of schemes, let $U_1, U_2$ be open subschemes of $A_0$, and let $q_1 \colon Y_1 \to \operatorname{Spec} T'$ and $q_2 \colon Y_2 \to \operatorname{Spec} T'$ be morphisms together with $g_1 \colon U_1 \to Y_1$ and $g_2 \colon U_2 \to Y_2$. Assume that for $i = 1, 2$ the square with top edge $g_i$, left edge $U_i \hookrightarrow A_0$ followed by $f_0$, right edge $q_i$ and bottom edge $\operatorname{Spec}(\pi)$ is cartesian. Write $p_1, p_2$ for the two projections of $A_0 \times_{\operatorname{Spec} T} A_0$ and put $W_0 := p_1^{-1}U_1 \sqcap p_2^{-1}U_2$, an open subscheme of that fibre product. Let $G_0 \colon W_0 \to Y_1 \times_{\operatorname{Spec} T'} Y_2$ be the morphism induced into the fibre product by the inclusion $W_0 \le p_1^{-1}U_1$ followed by the restriction $p_1 \mid_{U_1} \colon p_1^{-1}U_1 \to U_1$ and then $g_1$, and by the inclusion $W_0 \le p_2^{-1}U_2$ followed by $p_2 \mid_{U_2}$ and then $g_2$ (these two composites agree after composing with $q_1$, resp. $q_2$, and $\operatorname{Spec}(\pi)$). Then the square with top edge $G_0$, left edge $W_0 \hookrightarrow A_0 \times_{\operatorname{Spec} T} A_0$ followed by $p_1$ and $f_0$, right edge the first projection of $Y_1 \times_{\operatorname{Spec} T'} Y_2$ followed by $q_1$, and bottom edge $\operatorname{Spec}(\pi)$ is cartesian. No hypothesis is imposed on $\pi$.
--
--   This is the statement that a fibre product of two cartesian local lifts along $\operatorname{Spec}(\pi)$ is again cartesian, on the open chart $W_0 = U_1 \times_{\operatorname{Spec} T} U_2$ of the self-product $A_0 \times_{\operatorname{Spec} T} A_0$. It is used in the construction of affine smooth local lifts over open subschemes of a fibre product, in [`AlgebraicGeometry.Smooth.exists_affine_smooth_local_lift_opens_pullback`](thm.html#AlgebraicGeometry.Smooth.exists_affine_smooth_local_lift_opens_pullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPullback_pullback_lift_morphismRestrict_of_isPullback
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
    (Y₁ Y₂ : Scheme.{u}) (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
    (g₁ : (↑U₁ : Scheme.{u}) ⟶ Y₁) (g₂ : (↑U₂ : Scheme.{u}) ⟶ Y₂)
    (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
    (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π))) :
    IsPullback (pullback.lift
        ((pullback f₀ f₀).homOfLE (inf_le_left : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁)
        ((pullback f₀ f₀).homOfLE (inf_le_right : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂)
        (by simp only [Category.assoc]; rw [hg₁.w, hg₂.w];
            simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, pullback.condition_assoc]) :
        (↑(pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) : Scheme.{u}) ⟶ pullback q₁ q₂)
      ((pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂).ι ≫ pullback.fst f₀ f₀ ≫ f₀)
      (pullback.fst q₁ q₂ ≫ q₁) (Spec.map (CommRingCat.ofHom π)) := by sorry
