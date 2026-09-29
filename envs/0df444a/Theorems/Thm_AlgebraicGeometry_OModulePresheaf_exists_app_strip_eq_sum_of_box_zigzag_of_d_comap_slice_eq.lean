-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/c21057f7-44c3-5ef3-8b73-cb00aefceb47
-- title:
--   Box zig-zag data force a coboundary on the slice
-- statement:
--   Fix a field $k$ and $k$-schemes: morphisms $f_X\colon X \to \operatorname{Spec} k$, $f_Y\colon Y \to \operatorname{Spec} k$, a section $x_0\colon \operatorname{Spec} k \to X$, morphisms $p_1\colon P \to X$, $p_2\colon P \to Y$, and a closed immersion $i_Y\colon Y \to P$ with $p_1\circ i_Y = x_0\circ f_Y$ and $p_2\circ i_Y = \mathrm{id}_Y$. Let $\mathcal W$ be an ordered affine cover of $P$, that is, a finite linearly ordered index set $\iota$ together with affine opens $W_i$ whose supremum is $\top$; for $s$ a strictly increasing map $\mathrm{Fin}(n+1)\to\iota$ write $W_s = \bigcap_j W_{s(j)}$, and let $i_Y^{-1}\mathcal W$ be the cover of $Y$ with the same index set and opens $V_i = i_Y^{-1}W_i$. Let $c$ be a $1$-cochain for the presheaf $U\mapsto\Gamma(P,U)$, viewed as a $k$-module presheaf via $p_1$ followed by $f_X$, so $c_t\in\Gamma(P,W_t)$ for each strictly increasing $t\colon\mathrm{Fin}\,2\to\iota$. Assume: the pullback $s\mapsto i_Y^*(c_s)$, restricted to $V_{s(0)}\cap V_{s(1)}$, is the degree-$0$ Čech differential of some $0$-cochain for $U\mapsto\Gamma(Y,U)$ on $i_Y^{-1}\mathcal W$; $U\subseteq X$ is open with $x_0^{-1}U = \top$; for all indices $i,t$ there are sections $\gamma_{i,t}$ of the box $W_t \cap p_1^{-1}U \cap p_2^{-1}V_i$ and, for strictly increasing $\sigma\colon\mathrm{Fin}\,2\to\iota$, sections $e_\sigma$ of the strip $p_1^{-1}U \cap p_2^{-1}V_\sigma$; the vertical relation, that for each index $i$ and each $t\colon\mathrm{Fin}\,2\to\iota$ the restriction of $c_t$ to the box $W_t\cap p_1^{-1}U\cap p_2^{-1}V_i$ equals $\sum_{j<2}(-1)^j\gamma_{i,\partial_j t}$ restricted to that box; and the horizontal relation, that for each $\sigma\colon\mathrm{Fin}\,2\to\iota$ and each index $t$ the restriction of $e_\sigma$ to the same box equals $\sum_{j<2}(-1)^j\gamma_{\partial_j\sigma,t}$ restricted there, where $\partial_j$ deletes the $j$-th entry. The conclusion: there are sections $g_i\in\Gamma\bigl(Y, i_Y^{-1}(p_1^{-1}U\cap p_2^{-1}V_i)\bigr)$ such that for every strictly increasing $\sigma\colon\mathrm{Fin}\,2\to\iota$ one has $i_Y^*(e_\sigma) = \sum_{j<2}(-1)^j g_{\partial_j\sigma}$, each term restricted along the $i_Y$-preimage of the inclusion of $p_1^{-1}U\cap p_2^{-1}V_\sigma$ into $p_1^{-1}U\cap p_2^{-1}V_{\partial_j\sigma}$.
--
--   This is the slice-detection step in a Čech-theoretic argument: a zig-zag datum $(\gamma,e)$ relating a $1$-cochain $c$ on a cover of $P$ to a cochain of strips over an open $U\ni x_0$ is transported along the section $i_Y$, where the boxes collapse to intersections for the single cover $i_Y^{-1}\mathcal W$ of $Y$ and the diagonal of $\gamma$ exhibits $i_Y^*e$ as a Čech coboundary. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_app_strip_eq_sum_of_box_zigzag_of_d_comap_slice_eq
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (x₀ : Spec (CommRingCat.of k) ⟶ X)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU₀ : x₀ ⁻¹ᵁ U = ⊤)
    (γ : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (e : ∀ σ : (𝒲.comap iY).Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ))
    (hV : ∀ (σ : (𝒲.comap iY).Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : (𝒲.comap iY).Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j)))).op).hom (γ ((𝒲.comap iY).face σ j) t)) :
    ∃ g : ∀ i : (𝒲.comap iY).Idx 0, Γ(Y, iY ⁻¹ᵁ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter i)),
      ∀ σ : (𝒲.comap iY).Idx (0 + 1), (iY.app (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ (𝒲.comap iY).inter σ)).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map iY.base).monotone (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone ((𝒲.comap iY).inter_le_inter_face σ j))))).op).hom (g ((𝒲.comap iY).face σ j)) := by sorry
