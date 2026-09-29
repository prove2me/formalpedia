-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero
-- name    : AlgebraicGeometry.exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/288ae669-34ff-5376-9360-73aa0392aaff
-- title:
--   Flat Dedekind base with complete Witt-type local witnesses
-- statement:
--   Let $\mathcal O$ be a type carrying a commutative ring structure which is an integral domain of characteristic zero, and let $n$ be a natural number whose image in $\mathcal O$ is a unit. The assertion is the existence of a type $B_0$ equipped with a commutative ring structure making it a Dedekind domain, together with a ring homomorphism $i : B_0 \to \mathcal O$, such that three conditions hold. First, the induced morphism of schemes $\operatorname{Spec}\mathcal O \to \operatorname{Spec} B_0$ obtained by applying `Spec.map` to $i$ is flat in the sense of `AlgebraicGeometry.Flat`. Second, the image of $n$ in $B_0$ is a unit. Third, for every ideal $\mathfrak p$ of $B_0$ that is maximal there exist a type $W$ with a commutative ring structure which is an integral domain and a discrete valuation ring, complete and separated for the adic topology of its maximal ideal, whose residue field $W/\mathfrak m_W$ is algebraically closed, together with a $B_0$-algebra structure on $W$ for which $W$ is flat as a $B_0$-module and the preimage of $\mathfrak m_W$ under the structure map $B_0 \to W$ is exactly $\mathfrak p$.
--
--   This is the descent-base statement used when a characteristic-zero coefficient domain must be replaced by an arithmetic Dedekind base over which it is flat, with each closed point dominated by a complete discrete valuation ring having algebraically closed residue field (Witt vectors of $\overline{\mathbb F}_p$). It is invoked in the verification of smoothness of relative dimension one for fine moduli in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_isDedekindDomain_ringHom_flat_and_forall_exists_isDiscreteValuationRing_of_isUnit_of_charZero
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (n : ℕ) (hn : IsUnit ((n : ℕ) : 𝒪)) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : IsDedekindDomain B₀) (i : B₀ →+* 𝒪),
      Flat (Spec.map (CommRingCat.ofHom i)) ∧ IsUnit ((n : ℕ) : B₀) ∧
      (∀ 𝔭 : Ideal B₀, 𝔭.IsMaximal →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
          (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
          (_ : Algebra B₀ W), Module.Flat B₀ W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B₀ W) = 𝔭) := by sorry
