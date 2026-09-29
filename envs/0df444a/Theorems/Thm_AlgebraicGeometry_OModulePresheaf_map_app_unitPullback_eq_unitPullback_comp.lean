-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp
-- name    : AlgebraicGeometry.OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/da645524-e73a-5d0d-95b0-e40209f7ca43
-- title:
--   Refined pull-back cochains compose along an affine morphism
-- statement:
--   Fix commutative rings $R$, $R'$, $R''$ and schemes $X$, $X'$, $Y$ together with morphisms $\pi_X \colon X \to \operatorname{Spec} R'$, $\pi_{X'} \colon X' \to \operatorname{Spec} R''$ and $\pi_Y \colon Y \to \operatorname{Spec} R$ (these fix the $R$-module structures on the presheaves of sections), a morphism $h \colon X \to Y$ and an affine morphism $g \colon X' \to X$. Let $\mathcal{W}$ and $\mathcal{K}$ be ordered affine covers of $X$ and of $Y$, that is, finite linearly ordered index sets together with affine opens whose supremum is $\top$, and let $\mathrm{lam} \colon \mathcal{W}.\iota \to \mathcal{K}.\iota$ satisfy $\mathcal{W}.U\,w \le h^{-1}(\mathcal{K}.U\,(\mathrm{lam}\,w))$ for all $w$, and likewise $(\mathcal{W}.\mathrm{comap}\ g).U\,w \le (g \gg h)^{-1}(\mathcal{K}.U\,(\mathrm{lam}\,w))$, where $\mathcal{W}.\mathrm{comap}\ g$ is the ordered affine cover of $X'$ with the same index set and opens $g^{-1}(\mathcal{W}.U\,i)$. Let $n \in \mathbb{N}$, let $z$ assign to each strictly monotone $(n+1)$-tuple $t$ of indices of $\mathcal{K}$ a section of $\mathcal{O}_Y$ over $\mathcal{K}.\mathrm{inter}\,t = \bigwedge_j \mathcal{K}.U\,(t_j)$, and let $s$ be a strictly monotone $(n+1)$-tuple of indices of $\mathcal{W}.\mathrm{comap}\ g$. Then the section $\mathrm{unitPullback}\ h\ \mathcal{W}\ \mathcal{K}\ \mathrm{lam}\ n\ z\ s$ over $\mathcal{W}.\mathrm{inter}\,s$ — by definition the sign of the sorting permutation of $\mathrm{lam} \circ s$ times the restriction of $h^{\sharp}(z(\mathcal{W}.\mathrm{sortIdx}\ \mathcal{K}\ \mathrm{lam}\ s))$, when $\mathrm{lam} \circ s$ is injective, and $0$ otherwise — pulled back by $g^{\sharp}$ on $\mathcal{W}.\mathrm{inter}\,s$ and then restricted along $(\mathcal{W}.\mathrm{comap}\ g).\mathrm{inter}\,s \le g^{-1}(\mathcal{W}.\mathrm{inter}\,s)$, coincides with $\mathrm{unitPullback}\ (g \gg h)\ (\mathcal{W}.\mathrm{comap}\ g)\ \mathcal{K}\ \mathrm{lam}\ n\ z\ s$.
--
--   This is the compatibility of the refined Čech pull-back of $0$-th-order sections (the cochains of the presheaf $U \mapsto \Gamma(\mathcal{O}, U)$) with composition of morphisms, in the shape needed when the target cover is replaced by its preimage under an affine morphism: the same index map, the same sorting permutation, the same sign and the same vanishing branch serve for $h$ and for $g \gg h$. It is used in the construction of the cochain-level identities for abelian schemes, where a refined pull-back must be compared chart by chart after base change along an affine morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X X' Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πX' : X' ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (g : X' ⟶ X) [IsAffineHom g]
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (hlam' : ∀ w : (𝒲.comap g).ι, (𝒲.comap g).U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒲.comap g).Idx n) :
    (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom
        ((g.app (𝒲.inter s)).hom (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s))
      = OModulePresheaf.unitPullback (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s := by sorry
