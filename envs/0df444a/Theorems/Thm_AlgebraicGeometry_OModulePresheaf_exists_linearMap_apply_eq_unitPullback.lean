-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/e1635270-75bc-5773-8d72-442b9a839e94
-- title:
--   R-linearity of the alternating Čech pull-back of functions
-- statement:
--   Let $R$ be a commutative ring and let $X$, $Y$ be schemes equipped with morphisms $\pi_X \colon X \to \operatorname{Spec} R$ and $\pi_Y \colon Y \to \operatorname{Spec} R$, and let $h \colon X \to Y$ satisfy $\pi_Y \circ h = \pi_X$. Let $\mathcal{W}$ be an ordered affine cover of $X$ and $\mathcal{K}$ one of $Y$ — that is, a finite linearly ordered index type together with affine opens whose supremum is $\top$ — and let $\mathrm{lam} \colon \mathcal{W}.\iota \to \mathcal{K}.\iota$ be a map with $\mathcal{W}.U(w) \le h^{-1}(\mathcal{K}.U(\mathrm{lam}\,w))$ for every $w$. Fix $n \in \mathbb{N}$. The degree-$n$ cochain groups of the $\mathcal{O}$-module presheaf `unit` are $\prod_s \Gamma(Y, \bigsqcap_j \mathcal{K}.U(s_j))$ over strictly increasing $(n+1)$-tuples $s$, and likewise for $X$ and $\mathcal{W}$; each group of sections carries the $R$-algebra structure induced by the structure morphism. The assertion is that there exists an $R$-linear map $L$ from the $\mathcal{K}$-cochains of `unit πY` to the $\mathcal{W}$-cochains of `unit πX` such that $L z = \mathrm{unitPullback}\,h\,\mathcal{W}\,\mathcal{K}\,\mathrm{lam}\,\mathrm{hlam}\,n\,z$ for every $z$; here the pull-back cochain is given at a tuple $s$ by $0$ when $\mathrm{lam} \circ s$ fails to be injective, and otherwise by the sign of the sorting permutation of $\mathrm{lam} \circ s$ times the restriction to $\bigsqcap_j \mathcal{W}.U(s_j)$ of $h^{\sharp}$ applied to the value of $z$ on the sorted tuple.
--
--   This records that the alternating pull-back of Čech cochains of structure sheaves along a morphism over $\operatorname{Spec} R$ is a morphism of $R$-modules, packaged as a bundled `LinearMap` so that kernels, images and quotients are available to consumers. It is used in the comparison of Čech classes under pull-back and in the obstruction-theoretic computations for Mumford bundles and abelian-scheme property bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    ∃ L : (OModulePresheaf.unit πY).cochain 𝒦 n →ₗ[R] (OModulePresheaf.unit πX).cochain 𝒲 n,
      ∀ z, L z = OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by sorry
