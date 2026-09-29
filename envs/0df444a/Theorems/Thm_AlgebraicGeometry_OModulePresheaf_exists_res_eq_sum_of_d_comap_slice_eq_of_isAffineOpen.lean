-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
-- name    : AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/53e9b802-0a4a-5d52-a2b0-b489ac020f74
-- title:
--   Čech 1-cocycles trivial on the slice bound over affine slabs
-- statement:
--   Let $k$ be a field and let $X$, $Y$, $P$ be schemes with structure morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$, both quasi-compact and separated. Assume that the ring map $k \to \Gamma(X, \mathcal O_X)$ obtained from $f_X$ on global sections (via the inverse of `Scheme.ΓSpecIso`) is bijective, and let $x_0 : \operatorname{Spec} k \to X$ be a section of $f_X$. Let $(p_1, p_2)$ exhibit $P$ as a pullback of $f_X$ and $f_Y$, and let $i_Y : Y \to P$ be a closed immersion with $p_1 \circ i_Y = x_0 \circ f_Y$ and $p_2 \circ i_Y = \mathrm{id}_Y$. Let $\mathcal W$ be an ordered affine cover of $P$: a finite linearly ordered index set $\iota$ together with affine opens $W_i$ whose supremum is $\top$; for a strictly monotone $s : \mathrm{Fin}(i+1) \to \iota$ write $W_s = \bigsqcap_j W_{s(j)}$. Let $c$ be a $1$-cochain for the structure-sheaf presheaf `OModulePresheaf.unit (p₁ ≫ fX)`, i.e. a family of sections $c_t \in \Gamma(P, W_t)$ indexed by strictly monotone $t : \mathrm{Fin}\,2 \to \iota$, annihilated by the differential `d` in degree $1$. Assume further that the pullback of $c$ along $i_Y$, namely $s \mapsto i_Y^{*}(c_s)$ restricted to $i_Y^{-1}W_s$, is the image under `d` in degree $0$ of some $0$-cochain for the cover $i_Y^{-1}\mathcal W$ on $Y$. Finally let $U \subseteq X$ be an affine open. Then there is a family $\beta_t \in \Gamma(P, W_t \sqcap p_1^{-1}U)$, indexed by the $0$-indices $t$ (strictly monotone maps $\mathrm{Fin}\,1 \to \iota$), such that for every $1$-index $t$ the restriction of $c_t$ to $W_t \sqcap p_1^{-1}U$ equals $\sum_{j : \mathrm{Fin}\,2} (-1)^j$ times the restriction of $\beta_{t \circ \widehat{\jmath}}$, where $t \circ \widehat{\jmath}$ is the $j$-th face of $t$.
--
--   This is the Künneth-type slab step: a Čech $1$-cocycle of $\mathcal O_P$ on a finite ordered affine cover of $P = X \times_k Y$ whose restriction to the slice $\{x_0\} \times Y$ is a coboundary becomes a coboundary after restriction to each slab $p_1^{-1}U = U \times_k Y$ with $U \subseteq X$ affine, under the hypothesis that $\Gamma(X, \mathcal O_X) = k$. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap), which globalises the conclusion from affine slabs to all of $P$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by sorry
