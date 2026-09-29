-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero
-- name    : AlgebraicGeometry.OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/30f0675a-f29d-5b96-8d26-8bc8adda7470
-- title:
--   Refinement pull-back independent of index map up to coboundary
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $X$ and $Y$ be schemes, let $\pi_X \colon X \to \operatorname{Spec} R'$ be a separated morphism and $\pi_Y \colon Y \to \operatorname{Spec} R$ any morphism, and let $h \colon X \to Y$ be a morphism of schemes. Let $\mathcal{W}$ be an ordered affine cover of $X$ and $\mathcal{K}$ one of $Y$, that is, finite linearly ordered index types together with affine open subsets whose supremum is the whole scheme. Let $\lambda, \lambda' \colon \mathcal{W}.\iota \to \mathcal{K}.\iota$ satisfy $\mathcal{W}.U(w) \le h^{-1}(\mathcal{K}.U(\lambda w))$ and $\mathcal{W}.U(w) \le h^{-1}(\mathcal{K}.U(\lambda' w))$ for all $w$. Fix $n \in \mathbb{N}$ and a degree-$n$ cochain $z$ for the presheaf `OModulePresheaf.unit` of $\pi_Y$ on $\mathcal{K}$ — a family assigning to each strictly increasing tuple $s$ of indices a section in $\Gamma(Y, \mathcal{K}.\mathrm{inter}\,s)$, where $\mathcal{K}.\mathrm{inter}\,s$ is the intersection of the corresponding members of the cover — and assume $z$ is a cocycle, $d_{\mathcal{K}}^{n} z = 0$. Each $\lambda$ induces a pull-back cochain `unitPullback` on $\mathcal{W}$ for the unit presheaf of $\pi_X$, whose value at $s$ is $0$ unless $\lambda \circ s$ is injective, and otherwise is the sign of the permutation sorting $\lambda \circ s$ times the restriction to $\mathcal{W}.\mathrm{inter}\,s$ of $h^\ast$ of the value of $z$ at the sorted tuple. The assertion is that the difference of the two pull-backs of $z$, along $\lambda$ and along $\lambda'$, lies in the $R'$-submodule of degree-$n$ cochains on $\mathcal{W}$ which is $\bot$ when $n = 0$ and is the range of $d_{\mathcal{W}}^{m}$ when $n = m + 1$; thus in degree $0$ the two pull-backs coincide, and in positive degree they differ by a coboundary.
--
--   This is the statement that two maps refining one ordered affine cover into another induce maps on alternating Čech cochains that agree on cocycles up to a coboundary, the cochain-level form of the classical independence of the refinement map in Čech theory. It is used to compare Čech cohomology for different covers and index maps, feeding the results on composites of pull-backs and on pull-back along a refinement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) [IsSeparated πX] (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam' w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (hz : (OModulePresheaf.unit πY).d 𝒦 n z = 0) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' n z
      ∈ (show Submodule R' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by sorry
