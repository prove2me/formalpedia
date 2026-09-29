-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
-- name    : AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/3f839110-1485-5ade-b5c5-f7454bb33eef
-- title:
--   Box zig-zag datum with bounding strip cochain yields slab coboundary
-- statement:
--   Let $k$ be a field and let $fX : X \to \operatorname{Spec} k$, $fY : Y \to \operatorname{Spec} k$ be separated morphisms of schemes, and let $p_1 : P \to X$, $p_2 : P \to Y$ exhibit $P$ as the pullback of $fX$ and $fY$. Let $\mathcal W$ be an ordered affine cover of $P$ and $\mathcal V$ one of $Y$ (a finite linearly ordered index set together with affine opens whose supremum is $\top$); for a strictly monotone $s : \mathrm{Fin}(i+1) \to$ the index set, write $\mathcal W.\mathrm{inter}\,s$ for the intersection of the corresponding opens and $\partial_j s$ for the $j$-th face. Let $c$ be a $1$-cochain for $\mathcal W$ with values in the presheaf of $k$-modules $\mathcal O_P$ (i.e. $c_t \in \Gamma(P, \mathcal W.\mathrm{inter}\,t)$ for each $t$ of length $2$), and let $U \subseteq X$ be an affine open. Suppose given sections $\gamma_{\sigma,t} \in \Gamma(P, \mathcal W.\mathrm{inter}\,t \cap p_1^{-1}U \cap p_2^{-1}\mathcal V.\mathrm{inter}\,\sigma)$ for all singletons $\sigma$ of $\mathcal V$ and $t$ of $\mathcal W$, and $e_\sigma \in \Gamma(P, p_1^{-1}U \cap p_2^{-1}\mathcal V.\mathrm{inter}\,\sigma)$ for all $\sigma$ of length $2$, such that: (V) for every singleton $\sigma$ and every $t$ of length $2$, the restriction of $c_t$ to the box equals $\sum_{j<2} (-1)^j \gamma_{\sigma,\partial_j t}$ restricted there; (H) for every $\sigma$ of length $2$ and every singleton $t$, the restriction of $e_\sigma$ to the box equals $\sum_{j<2} (-1)^j \gamma_{\partial_j\sigma,t}$ restricted there; and (he) $e$ is a coboundary on the strips, i.e. there are $g_i \in \Gamma(P, p_1^{-1}U \cap p_2^{-1}\mathcal V.\mathrm{inter}\,i)$ with $e_\sigma = \sum_{j<2} (-1)^j g_{\partial_j \sigma}$ restricted, for all $\sigma$ of length $2$. Then there exist sections $\beta_t \in \Gamma(P, \mathcal W.\mathrm{inter}\,t \cap p_1^{-1}U)$, indexed by the singletons $t$ of $\mathcal W$, such that for every $t$ of length $2$ the restriction of $c_t$ to $\mathcal W.\mathrm{inter}\,t \cap p_1^{-1}U$ equals $\sum_{j<2} (-1)^j \beta_{\partial_j t}$ restricted there.
--
--   This is the diagonal (zig-zag) step for the Čech double complex attached to the two families of opens $(W_t \cap p_1^{-1}U)_t$ and $(p_1^{-1}U \cap p_2^{-1}V_i)_i$ of $p_1^{-1}U$: a bidegree $(0,0)$ datum $\gamma$ linking the $1$-cochain $c$ to a strip cochain $e$ that already bounds forces $c$ to bound on the slabs $W_t \cap p_1^{-1}U$, the correction being glued from the $\mathcal V$-cocycle condition. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen), and relies on exactness of the ordered-affine-cover Čech complex in degree $0$ (`ker_d_zero_eq_range_aug` and `aug_injective`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
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
    (he : ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (g (𝒱.face σ j))) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by sorry
