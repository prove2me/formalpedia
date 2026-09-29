-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.d_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/4f129326-6e9c-5562-83cc-53aa9ae9308a
-- title:
--   Refinement pull-back of Čech cochains is a chain map
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $X$ and $Y$ be schemes, and let $\pi_X \colon X \to \operatorname{Spec} R'$ and $\pi_Y \colon Y \to \operatorname{Spec} R$ be morphisms (used only to equip the section rings with their algebra structures). Let $h \colon X \to Y$ be a morphism of schemes, let $\mathcal W$ and $\mathcal K$ be ordered affine covers of $X$ and $Y$ respectively — that is, finite linearly ordered index types together with affine opens whose supremum is $\top$ — and let $\mathrm{lam} \colon \mathcal W.\iota \to \mathcal K.\iota$ satisfy $\mathcal W.U\,w \le h^{-1}(\mathcal K.U(\mathrm{lam}\,w))$ for every $w$. Fix $n \in \mathbb N$ and an $n$-cochain $z$ for the presheaf `OModulePresheaf.unit πY`, i.e. a family assigning to each index $s$ of $\mathcal K.\mathrm{Idx}\ n$ an element of $\Gamma(Y, \bigsqcap_j \mathcal K.U(s.1\,j))$. Then the Čech differential `OModulePresheaf.d` for `unit πX` on $\mathcal W$ in degree $n$, applied to the pull-back `OModulePresheaf.unitPullback h 𝒲 𝒦 lam hlam n z`, equals the pull-back in degree $n+1$ of the differential `OModulePresheaf.d` for `unit πY` on $\mathcal K$ applied to $z$. Here the pull-back of a cochain sends an index $s$ to zero when $\mathrm{lam} \circ s.1$ fails to be injective, and otherwise to the sign of the sorting permutation of $\mathrm{lam} \circ s.1$ times the restriction, along the inclusion of $\mathcal W$-intersection into the $h$-preimage of the corresponding sorted $\mathcal K$-intersection, of the image under $h$ of the value of $z$ at that sorted index.
--
--   This is the statement that the refinement map induced by an index map $\mathrm{lam}$, in the model of alternating cochains indexed by strictly increasing chains, is a morphism of Čech complexes from the structure-sheaf complex of $\mathcal K$ on $Y$ to that of $\mathcal W$ on $X$. It is what allows the resulting map on cohomology to be formed, and is used by the comparison results for Čech cohomology of different covers and for pinned or product covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback.lean

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

theorem AlgebraicGeometry.OModulePresheaf.d_unitPullback
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).d 𝒲 n (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).d 𝒦 n z) := by sorry
