-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
-- name    : AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/b153388d-0af8-5e23-a1cf-776789f0e4a8
-- title:
--   Box zig-zag datum for a Čech 1-cocycle over an affine open
-- statement:
--   Let $k$ be a field, let $fX : X \to \operatorname{Spec} k$ and $fY : Y \to \operatorname{Spec} k$ be quasi-compact separated morphisms of schemes, and let $p_1 : P \to X$, $p_2 : P \to Y$ exhibit $P$ as the pullback of $fX$ and $fY$, so $P = X \times_k Y$. Let $\mathcal{W}$ be an ordered affine cover of $P$ and $\mathcal{V}$ one of $Y$: each consists of a finite linearly ordered index type together with affine opens whose supremum is the whole space; for $i \ge 0$, $\mathcal{W}.\mathrm{Idx}\,i$ is the set of strictly monotone maps $\mathrm{Fin}(i+1) \to \mathcal{W}.\iota$, $\mathcal{W}.\mathrm{inter}$ is the intersection of the corresponding opens, and $\mathcal{W}.\mathrm{face}$ deletes the $j$-th index. Let $c$ be a $1$-cochain for the presheaf of $\mathcal{O}$-modules $\mathrm{unit}(p_1 \circ fX)$, i.e. a family $c_t \in \Gamma(P, \mathcal{W}.\mathrm{inter}\,t)$ indexed by pairs $t$ of indices of $\mathcal{W}$, with vanishing differential, and let $U \subseteq X$ be an affine open. Then there are a family $\gamma_{\sigma,t} \in \Gamma(P, \mathcal{W}.\mathrm{inter}\,t \cap p_1^{-1}U \cap p_2^{-1}\mathcal{V}.\mathrm{inter}\,\sigma)$ indexed by single indices $\sigma$ of $\mathcal{V}$ and $t$ of $\mathcal{W}$, and a family $e_\sigma \in \Gamma(P, p_1^{-1}U \cap p_2^{-1}\mathcal{V}.\mathrm{inter}\,\sigma)$ indexed by pairs $\sigma$ of indices of $\mathcal{V}$, such that, with all restrictions along the evident inclusions taken by the structure sheaf of $P$: for every single index $\sigma$ of $\mathcal{V}$ and every pair $t$ of $\mathcal{W}$, the restriction of $c_t$ equals $\sum_{j<2}(-1)^j \gamma_{\sigma,\mathcal{W}.\mathrm{face}(t,j)}$; for every pair $\sigma$ of $\mathcal{V}$ and every single index $t$ of $\mathcal{W}$, the restriction of $e_\sigma$ equals $\sum_{j<2}(-1)^j \gamma_{\mathcal{V}.\mathrm{face}(\sigma,j),t}$; and for every triple $\rho$ of indices of $\mathcal{V}$, $\sum_{j<3}(-1)^j e_{\mathcal{V}.\mathrm{face}(\rho,j)}$ restricted to $p_1^{-1}U \cap p_2^{-1}\mathcal{V}.\mathrm{inter}\,\rho$ vanishes.
--
--   This is the zig-zag step in the Čech double complex attached to the two families of opens $(\mathcal{W}.\mathrm{inter}\,t \cap p_1^{-1}U)_t$ and $(p_1^{-1}U \cap p_2^{-1}\mathcal{V}.\mathrm{inter}\,\sigma)_\sigma$ of $p_1^{-1}U \subseteq X \times_k Y$: the $1$-cocycle $c$, restricted to the affine strips $U \times_k V_\sigma$, is written as a vertical coboundary of $\gamma$ whose horizontal differential is a $\mathcal{V}$-cocycle $e$. It rests on the vanishing of Čech cohomology of the structure sheaf on an affine open ([`AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen`](thm.html#AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen), together with the exactness of the augmentation at degree zero), and is used by [`AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
      (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)),
      (∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
        (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
                (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t j))) ∧
      (∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
        (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
                ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t)) ∧
      (∀ ρ : 𝒱.Idx (1 + 1),
        ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face ρ j)))).op).hom (e (𝒱.face ρ j)) = 0) := by sorry
