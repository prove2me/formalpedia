-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply
-- name    : AlgebraicGeometry.OModulePresheaf.unitPullback_comap_id_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/3a73fd1d-fec1-5a26-a4ba-d8c575436c0b
-- title:
--   Pull-back of unit cochains along an affine morphism
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $X$ and $Y$ be schemes, and let $\pi_X \colon X \to \operatorname{Spec} R'$ and $\pi_Y \colon Y \to \operatorname{Spec} R$ be morphisms, so that the structure sheaves carry the corresponding algebra structures. Let $h \colon X \to Y$ be an affine morphism and let $\mathcal{K}$ be an ordered affine cover of $Y$, that is, a finite linearly ordered index type $\mathcal{K}.\iota$ together with opens $\mathcal{K}.U_i \subseteq Y$ that are affine and satisfy $\bigsqcup_i \mathcal{K}.U_i = \top$. Write $\mathcal{K}.\mathrm{comap}\ h$ for the ordered affine cover of $X$ with the same index type and order and with charts $h^{-1}(\mathcal{K}.U_i)$, and assume $hlam$: for each index $w$, $(\mathcal{K}.\mathrm{comap}\ h).U_w \le h^{-1}(\mathcal{K}.U_w)$. Let $n \in \mathbb{N}$, let $z$ be an $n$-cochain for the unit $\mathcal{O}$-module presheaf on $Y$ relative to $\mathcal{K}$, i.e. a family assigning to each strictly increasing $s \colon \mathrm{Fin}(n+1) \to \mathcal{K}.\iota$ a section $z(s) \in \Gamma(Y, \bigwedge_j \mathcal{K}.U_{s(j)})$, and let $s$ be such a chain for $\mathcal{K}.\mathrm{comap}\ h$. Then the alternating pull-back `unitPullback` of $z$ along $h$ with index map the identity, evaluated at $s$, equals the image of $z(s)$ under $h$'s comparison map `h.app` on $\mathcal{K}.\mathrm{inter}\ s$ followed by the presheaf restriction from $h^{-1}(\mathcal{K}.\mathrm{inter}\ s)$ to $(\mathcal{K}.\mathrm{comap}\ h).\mathrm{inter}\ s$ given by `𝒦.comap_inter_le h s`.
--
--   This identifies the general alternating Čech pull-back of cochains, defined with a sign coming from sorting the image index tuple and with a zero branch for non-injective tuples, with the naive chartwise pull-back in the special case where the target cover is the comapped cover and the index map is the identity. It is used in the study of $H^0$/$H^1$ comparisons for the comapped cover, notably by [`GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_comap_id_apply
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) [IsAffineHom h] (𝒦 : Y.OrderedAffineCover)
    (hlam : ∀ w : (𝒦.comap h).ι, (𝒦.comap h).U w ≤ h ⁻¹ᵁ 𝒦.U w)
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒦.comap h).Idx n) :
    OModulePresheaf.unitPullback (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam n z s =
      (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) := by sorry
