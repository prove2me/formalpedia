-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext
-- name    : AlgebraicGeometry.OModulePresheaf.ores_ounitPullback_oext
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/2c8b8bff-455f-59a3-9e55-4d5b3fc8b699
-- title:
--   Refined Čech pull-back factors through ordered cochains
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $X$ and $Y$ be schemes, and let $\pi_X : X \to \operatorname{Spec} R'$, $\pi_Y : Y \to \operatorname{Spec} R$ and $h : X \to Y$ be morphisms of schemes. Let $\mathcal{W}$ be an ordered affine cover of $X$ and $\mathcal{K}$ one of $Y$ (each a finite, linearly ordered index set together with affine opens whose supremum is $\top$), let $\mathrm{lam} : \mathcal{W}.\iota \to \mathcal{K}.\iota$ satisfy $\mathcal{W}.U\,w \le h^{-1}(\mathcal{K}.U\,(\mathrm{lam}\,w))$ for all $w$, let $n \in \mathbb{N}$, and let $z$ be an $n$-cochain for the presheaf `unit` $\pi_Y$ of $R$-modules attached to $\pi_Y$ (whose sections over an open $U$ are $\Gamma(Y,U)$), i.e. a family assigning to each strictly monotone $s : \mathrm{Fin}(n+1) \to \mathcal{K}.\iota$ a section over $\bigsqcap_j \mathcal{K}.U\,(s\,j)$. The conclusion asserts the equality of two $n$-cochains on $\mathcal{W}$ for `unit` $\pi_X$: first pass from $z$ to the ordered cochain `oext`, sending an arbitrary tuple $t$ to $\operatorname{sign}(\mathrm{sort}\,t)$ times the restriction of $z$ at the sorted tuple, and to $0$ when $t$ is not injective; pull back along $h$ by `ounitPullback`, i.e. $t \mapsto$ the restriction to $\mathcal{W}.\mathrm{ointer}\,t$ of $h^{\#}$ applied to the value at $\mathrm{lam} \circ t$; then restrict via `ores` to strictly monotone tuples. This agrees with `unitPullback` of $z$, whose value at a strictly monotone $s$ is $\operatorname{sign}(\mathrm{sort}(\mathrm{lam} \circ s))$ times the restriction of $h^{\#}(z(\mathcal{W}.\mathrm{sortIdx}\,\mathcal{K}\,\mathrm{lam}\,s))$ when $\mathrm{lam} \circ s$ is injective, and $0$ otherwise.
--
--   This is the compatibility of the sign-refined Čech pull-back on ordered (strictly monotone) index tuples with the standard comparison between alternating cochains on arbitrary tuples and cochains on monotone tuples: the refined pull-back is the composite of alternating extension, ordered pull-back and restriction. It is used in the iterated Čech and Leray constructions for the structure-sheaf cochain complexes, in the identification of total and Čech differentials and cup products there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.ores_ounitPullback_oext
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by sorry
