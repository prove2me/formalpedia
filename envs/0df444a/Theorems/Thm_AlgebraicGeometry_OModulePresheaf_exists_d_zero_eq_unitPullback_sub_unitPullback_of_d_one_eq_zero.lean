-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/b7894577-0c9b-54a7-a646-84f42817d689
-- title:
--   Degree-one Čech pull-back independent of the refining index map
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $X$ and $Y$ be schemes, and let $\pi_X : X \to \operatorname{Spec} R'$ and $\pi_Y : Y \to \operatorname{Spec} R$ be morphisms, so that the structure sheaves $\Gamma(X,-)$ and $\Gamma(Y,-)$ carry the $R'$- resp. $R$-algebra structures of `OModulePresheaf.unit`, whose objects are the section rings $\Gamma(-,U)$ with the presheaf restriction maps. Let $h : X \to Y$ be a morphism, let $\mathcal W$ and $\mathcal K$ be ordered affine covers of $X$ and $Y$ (a finite linearly ordered index type together with affine opens whose supremum is $\top$), and let $\lambda, \lambda' : \mathcal W.\iota \to \mathcal K.\iota$ be two index maps refining $h$, in the sense that $\mathcal W.U(w) \le h^{-1}(\mathcal K.U(\lambda w))$ and $\mathcal W.U(w) \le h^{-1}(\mathcal K.U(\lambda' w))$ for every $w$. Let $z$ be a $1$-cochain for `unit`$\pi_Y$ on $\mathcal K$, i.e. a family of sections of $\Gamma(Y, \bigsqcap_j \mathcal K.U(s_j))$ indexed by the strictly monotone tuples $s \in \mathcal K.\mathrm{Idx}\,1$, and assume $z$ is a cocycle, $d^1 z = 0$. Then there exists a $0$-cochain $b$ for `unit`$\pi_X$ on $\mathcal W$ with $d^0 b = \lambda^{*}z - \lambda'^{*}z$, where $\lambda^{*}$ denotes `unitPullback`: on an index $s$ it is zero unless $\lambda \circ s$ is injective, and otherwise the sign of the sorting permutation times the restriction to $\mathcal W.\mathrm{inter}\,s$ of $h^\sharp$ applied to the value of $z$ at the sorted index.
--
--   This is the degree-one case of the classical statement that two maps refining a cover induce cochain-homotopic pull-backs on alternating Čech cochains, here for the cochain complexes of the structure presheaf of a scheme over an affine base. It is used in the construction of descent data for abelian schemes, being cited by [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_inv_add_unitPullback_id_of_d_one_eq_zero) and [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_d_eq_unitPullback_mul_sub_fst_sub_snd_of_d_one_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_d_zero_eq_unitPullback_sub_unitPullback_of_d_one_eq_zero
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam' w))
    (z : (OModulePresheaf.unit πY).cochain 𝒦 1) (hz : (OModulePresheaf.unit πY).d 𝒦 1 z = 0) :
    ∃ b : (OModulePresheaf.unit πX).cochain 𝒲 0,
      (OModulePresheaf.unit πX).d 𝒲 0 b =
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 1 z - OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' 1 z := by sorry
