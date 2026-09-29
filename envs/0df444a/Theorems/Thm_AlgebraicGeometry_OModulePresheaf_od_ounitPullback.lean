-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_od_ounitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.od_ounitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4ce26d68-6eb3-58ed-80f2-c47ad032a551
-- title:
--   Ordered Čech pull-back of functions commutes with d
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $X$ and $Y$ be schemes, and let $\pi_X : X \to \operatorname{Spec} R'$ and $\pi_Y : Y \to \operatorname{Spec} R$ be morphisms; these endow each $\Gamma(X,U)$ with an $R'$-algebra structure and each $\Gamma(Y,W)$ with an $R$-algebra structure, which is what the presheaves of modules `OModulePresheaf.unit` $\pi_X$ and `OModulePresheaf.unit` $\pi_Y$ record (their sections over an open are the ring sections, with restriction maps the presheaf restrictions). Let $h : X \to Y$ be a morphism, let $\mathcal{W}$ and $\mathcal{K}$ be ordered affine covers of $X$ and $Y$ (finite linearly ordered index sets, affine opens whose supremum is $\top$), let $\lambda : \mathcal{W}.\iota \to \mathcal{K}.\iota$ satisfy $\mathcal{W}.U(w) \le h^{-1}(\mathcal{K}.U(\lambda w))$ for all $w$, let $n \in \mathbb{N}$, and let $c$ be an ordered $n$-cochain for $\mathcal{K}$, i.e. a family $c(t) \in \Gamma(Y, \bigsqcap_j \mathcal{K}.U(t_j))$ indexed by $t : \operatorname{Fin}(n+1) \to \mathcal{K}.\iota$. Then the pull-back `ounitPullback`, which sends such a $c$ to the cochain $t \mapsto$ (the restriction to $\bigsqcap_j \mathcal{W}.U(t_j)$ of the image of $c(\lambda \circ t)$ under $h^\sharp$ on $\Gamma(Y,\bigsqcap_j\mathcal{K}.U(\lambda t_j))$), commutes with the alternating-sum differentials `od`: $d_{\mathcal{W}}(h^\ast c) = h^\ast(d_{\mathcal{K}} c)$ as ordered $(n+1)$-cochains for $\mathcal{W}$ with values in `unit` $\pi_X$.
--
--   This is the statement that pull-back along $h$, implemented on ordered (alternating-index) Čech cochains via the index map $\lambda$, is a map of cochain complexes for the structure sheaves, the simplicial map $t \mapsto \lambda \circ t$ commuting with the face maps on the nose. It is used in the comparison of cup products under pull-back, in `unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_od_ounitPullback.lean

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

theorem AlgebraicGeometry.OModulePresheaf.od_ounitPullback
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (c : (OModulePresheaf.unit πY).ocochain 𝒦 n) :
    (OModulePresheaf.unit πX).od 𝒲 n (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c) =
      OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).od 𝒦 n c) := by sorry
