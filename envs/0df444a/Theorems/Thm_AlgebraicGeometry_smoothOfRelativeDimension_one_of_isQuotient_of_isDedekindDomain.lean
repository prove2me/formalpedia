-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/0211b760-e6a5-5c08-bed5-7c73e4bff291
-- title:
--   Smoothness of a finite quotient of a relative curve over a Dedekind base
-- statement:
--   Let $B$ be a Dedekind domain and let $M$, $X$ be schemes (in the bottom universe). Let $\pi_M : M \to \operatorname{Spec} B$ be smooth of relative dimension $1$, let $G$ be a finite group, and let $\rho : G \to \operatorname{Aut}(M)$ be a homomorphism such that each automorphism $\rho(g)$ followed by $\pi_M$ equals $\pi_M$, i.e. the action is over $B$. Assume the witness hypothesis: for every maximal ideal $\mathfrak p$ of $B$ there exist a ring $W$ which is a domain and a discrete valuation ring, complete with respect to the adic filtration of its maximal ideal, with algebraically closed residue field, together with a $B$-algebra structure on $W$ making $W$ flat as a $B$-module and such that the contraction of the maximal ideal of $W$ along $B \to W$ is $\mathfrak p$. Let $\pi : M \to X$ and $\pi_X : X \to \operatorname{Spec} B$ satisfy $\pi$ followed by $\pi_X$ equals $\pi_M$, with $\pi$ invariant ($\rho(g)$ followed by $\pi$ equals $\pi$ for all $g$), affine and surjective, and assume that $\pi$ exhibits $X$ as the quotient of $M$ by $G$ in the sheaf-theoretic sense: for every open $V \subseteq X$ the ring map $\pi^{*}$ on sections over $V$ is injective with image exactly the sections of $M$ over $\pi^{-1}V$ fixed by all the induced maps of $\rho(g)$, and every affine open $U \subseteq M$ with $\rho(g)^{-1}U = U$ for all $g$ is of the form $\pi^{-1}V$ for some affine open $V \subseteq X$. Then $\pi_X : X \to \operatorname{Spec} B$ is smooth of relative dimension $1$. No hypothesis is imposed on the orders of the stabilisers of the action.
--
--   This is the wild case of the standard statement that the quotient of a smooth relative curve by a finite group of automorphisms over a base is again smooth of relative dimension one (as in Deligne–Rapoport and Katz–Mazur), here with a Dedekind base equipped with complete discrete valuation ring witnesses at each closed point in place of any tameness assumption; it reduces to the affine-chart, ring-theoretic statement [`AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain). It is used to prove smoothness of the quaternionic fine moduli scheme in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain
    {B : Type} [CommRing B] [IsDedekindDomain B]
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B)) [SmoothOfRelativeDimension 1 πM]
    (G : Type) [Group G] [Fintype G] (ρ : G →* Aut M) (hρ : ∀ g : G, (ρ g).hom ≫ πM = πM)
    (hW : ∀ 𝔭 : Ideal B, 𝔭.IsMaximal →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
        (_ : Algebra B W), Module.Flat B W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B W) = 𝔭)
    (π : M ⟶ X) (πX : X ⟶ Spec (CommRingCat.of B)) (hπX : π ≫ πX = πM)
    (hπ : ∀ g : G, (ρ g).hom ≫ π = π) [IsAffineHom π] [Surjective π]
    (hsec_inj : ∀ V : X.Opens, Function.Injective (π.app V))
    (hsec : ∀ V : X.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (haff : ∀ U : M.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) →
        ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) :
    SmoothOfRelativeDimension 1 πX := by sorry
