-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent
-- name    : AlgebraicGeometry.Smooth.exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/7712fe95-402f-5f5d-94d1-2b54ffd5dd18
-- title:
--   Local smooth lifting over a nilpotent thickening of an affine base
-- statement:
--   Let $\pi \colon T' \to T$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal, and let $P$, $P_0$, $A$ be schemes with $P$ affine. Given structure morphisms $p \colon P \to \operatorname{Spec} T'$ and $p_0 \colon P_0 \to \operatorname{Spec} T$ together with $G \colon P_0 \to P$ such that the square formed by $G$, $p_0$, $p$ and $\operatorname{Spec}(\pi)$ is a pullback square (so $P_0 \cong P \times_{\operatorname{Spec} T'} \operatorname{Spec} T$ is the closed subscheme cut out by the nilpotent kernel), and given a smooth morphism $f \colon A \to \operatorname{Spec} T'$ and a morphism $\mu \colon P_0 \to A$ with $\mu$ followed by $f$ equal to $p_0$ followed by $\operatorname{Spec}(\pi)$, the assertion is the existence of: a finite linearly ordered family $(U_i)_{i \in \iota}$ of affine open subschemes of $P$ with $\bigsqcup_i U_i = \top$ (that is, a term of `P.OrderedAffineCover`); global sections $a_i \in \Gamma(P, \top)$ with $U_i = P.\mathrm{basicOpen}(a_i)$ for every $i$; and morphisms $m_i \colon U_i \to A$ such that $m_i$ followed by $f$ equals the inclusion $U_i \hookrightarrow P$ followed by $p$ (so each $m_i$ is a morphism over $T'$), and the restriction $G \mid_{U_i} \colon G^{-1}(U_i) \to U_i$ followed by $m_i$ equals the inclusion $G^{-1}(U_i) \hookrightarrow P_0$ followed by $\mu$, i.e. $m_i$ lifts $\mu$ across the thickening $G^{-1}(U_i) \hookrightarrow U_i$.
--
--   This is the local form of the infinitesimal lifting property of smooth morphisms (formal smoothness along nilpotent ideals), packaged so that the charts of the cover are basic opens of the affine scheme $P$ and are indexed by a finite linearly ordered set, which is the shape needed to form Čech cochains. It is used in the construction of charts lifting a bare deformation datum, where the discrepancies between the local lifts $m_i$ give rise to an obstruction cocycle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_orderedAffineCover_basicOpen_forall_lift_comp_eq_of_isAffine_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} [IsAffine P] (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) [Smooth f] (μ : P₀ ⟶ A)
    (hμ : μ ≫ f = p₀ ≫ Spec.map (CommRingCat.ofHom π)) :
    ∃ (𝒲 : P.OrderedAffineCover) (a : 𝒲.ι → Γ(P, ⊤)) (_ : ∀ i : 𝒲.ι, 𝒲.U i = P.basicOpen (a i))
      (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A),
      (∀ i, m i ≫ f = (𝒲.U i).ι ≫ p) ∧ (∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ) := by sorry
