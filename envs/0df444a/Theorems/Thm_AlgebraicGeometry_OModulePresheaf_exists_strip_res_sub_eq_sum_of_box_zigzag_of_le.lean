-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
-- name    : AlgebraicGeometry.OModulePresheaf.exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/73a0cf7a-8aff-5f8d-a032-9500fa840b8b
-- title:
--   Comparison of two box zig-zag data over nested affine opens
-- statement:
--   Let $k$ be a field and let $X$, $Y$, $P$ be schemes, with separated structure morphisms $f_X\colon X\to\operatorname{Spec} k$ and $f_Y\colon Y\to\operatorname{Spec} k$, and with $p_1\colon P\to X$, $p_2\colon P\to Y$ forming a pullback square over $f_X$, $f_Y$ (so $P=X\times_kY$). Let $\mathcal W$ be an ordered affine cover of $P$ and $\mathcal V$ one of $Y$: each consists of a finite linearly ordered index set together with affine opens whose supremum is $\top$; for $i\in\mathbb N$ the index type $\mathcal V.\mathrm{Idx}\,i$ consists of strictly monotone maps $\mathrm{Fin}(i+1)\to\mathcal V.\iota$, $\mathcal V.\mathrm{inter}$ denotes the intersection of the corresponding opens, and $\mathcal V.\mathrm{face}$ omits one index. Let $c$ be a $1$-cochain for $\mathcal W$ of the presheaf `OModulePresheaf.unit` attached to $p_1$ followed by $f_X$, i.e. a family $c_t\in\Gamma(P,\mathcal W.\mathrm{inter}\,t)$ indexed by $t\in\mathcal W.\mathrm{Idx}\,1$. Let $U$ be an affine open of $X$ and let $\gamma$ be a family $\gamma_{\sigma,t}\in\Gamma\bigl(P,\mathcal W.\mathrm{inter}\,t\sqcap p_1^{-1}U\sqcap p_2^{-1}\mathcal V.\mathrm{inter}\,\sigma\bigr)$ for $\sigma\in\mathcal V.\mathrm{Idx}\,0$, $t\in\mathcal W.\mathrm{Idx}\,0$, and $e$ a family $e_\sigma\in\Gamma\bigl(P,p_1^{-1}U\sqcap p_2^{-1}\mathcal V.\mathrm{inter}\,\sigma\bigr)$ for $\sigma\in\mathcal V.\mathrm{Idx}\,1$, subject to two conditions: for all $\sigma\in\mathcal V.\mathrm{Idx}\,0$ and $t\in\mathcal W.\mathrm{Idx}\,1$ the restriction of $c_t$ to $\mathcal W.\mathrm{inter}\,t\sqcap p_1^{-1}U\sqcap p_2^{-1}\mathcal V.\mathrm{inter}\,\sigma$ equals $\sum_{j\in\mathrm{Fin}\,2}(-1)^j$ times the restriction of $\gamma_{\sigma,\mathcal W.\mathrm{face}\,t\,j}$; and for all $\sigma\in\mathcal V.\mathrm{Idx}\,1$ and $t\in\mathcal W.\mathrm{Idx}\,0$ the restriction of $e_\sigma$ to that same open equals $\sum_{j\in\mathrm{Fin}\,2}(-1)^j$ times the restriction of $\gamma_{\mathcal V.\mathrm{face}\,\sigma\,j,\,t}$. Let $U'\le U$ be a further affine open of $X$ and let $\gamma'$, $e'$ be data of the same shape over $U'$ satisfying the two analogous conditions with the same cochain $c$. Then there is a family $g_i\in\Gamma\bigl(P,p_1^{-1}U'\sqcap p_2^{-1}\mathcal V.\mathrm{inter}\,i\bigr)$, $i\in\mathcal V.\mathrm{Idx}\,0$, such that for every $\sigma\in\mathcal V.\mathrm{Idx}\,1$ the difference of the restriction of $e_\sigma$ to $p_1^{-1}U'\sqcap p_2^{-1}\mathcal V.\mathrm{inter}\,\sigma$ and $e'_\sigma$ equals $\sum_{j\in\mathrm{Fin}\,2}(-1)^j$ times the restriction of $g_{\mathcal V.\mathrm{face}\,\sigma\,j}$.
--
--   This is the naturality statement for the zig-zag construction in the Čech double complex attached to the two families of opens $(\mathcal W_t\cap p_1^{-1}U)_t$ and $(p_1^{-1}U\cap p_2^{-1}V_i)_i$ of $p_1^{-1}U$: two box zig-zag data for the same $1$-cochain $c$, one over $U$ and one over a smaller affine open $U'$, produce strip cochains that differ by a Čech coboundary for the cover of $p_1^{-1}U'$ by the strips. It feeds the construction of compatible strip cochains in [`AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen), and rests on the exactness of the ordered Čech complex of an affine open under a separated morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t))
    (U' : X.Opens) (hU' : IsAffineOpen U') (hle : U' ≤ U)
    (γ' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e' : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U') (𝒲.inter_le_inter_face t j)))).op).hom (γ' σ (𝒲.face t j)))
    (hH' : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e' σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U')
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ' (𝒱.face σ j) t)) :
    ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          ((TopologicalSpace.Opens.map p₁.base).monotone (hle)) : p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ) - e' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U')
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j)) := by sorry
