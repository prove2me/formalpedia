-- Prove2me | Theorems.Thm_AdicCompletion_isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
-- name    : AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/3ad6999e-9a49-53d1-b9a6-f82237deb092
-- title:
--   Analytic normality at a tame point of a finite cover
-- statement:
--   Let $A_2 \subseteq A_1$ be Noetherian commutative rings with $A_1$ a module-finite $A_2$-algebra whose structure map is injective, and assume $A_1$ is an integrally closed domain. Let $G$ be a finite group acting faithfully on $A_1$ by ring automorphisms, commuting with the $A_2$-action, such that every $G$-invariant element of $A_1$ comes from $A_2$. Let $y$ be a maximal ideal of $A_1$ and $\mathfrak p$ a prime of $A_2$ with $y \cap A_2 = \mathfrak p$. Let $e > 0$ be a natural number such that the inertia subgroup `y.inertia G` has cardinality $e$ and is cyclic. Let $\mathfrak Q_0 \subseteq \mathfrak p$ be a prime of $A_2$ and $\varpi \in A_2$. Let $O$ be a Noetherian local $A_2$-algebra realising the localisation of $A_2$ at $\mathfrak p$, and $s \in O$ with $\mathfrak Q_0 O = (s)$, maximal ideal $(\varpi, s)$, Krull dimension $2$, and $e$ invertible in $O$. Assume $A_1$ is unramified over $A_2$ at every height-one prime $\mathfrak Q \subseteq y$ with $\mathfrak Q \cap A_2 \neq \mathfrak Q_0$, and that $A_1/y$ is separable over $A_2/\mathfrak p$. Then for every local ring $S$ realising the localisation of $A_1$ at $y$, the adic completion of $S$ at its maximal ideal is an integrally closed domain.
--
--   This is the analytic normality statement at a tame point of a finite group quotient of a regular two-dimensional local germ: the completion of the local ring at a closed point $y$ whose inertia is cyclic of order invertible in the base, with ramification concentrated along the divisor cut out by $s$, is a normal domain. It supplies the normality input used in the study of the fibres of the relevant modular curve model, being cited by [`ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_off_section_xH_of_isSeparable`](thm.html#ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_off_section_xH_of_isSeparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame
    {A₂ A₁ : Type} [CommRing A₂] [CommRing A₁] [IsNoetherianRing A₂] [IsNoetherianRing A₁] [IsDomain A₁] [IsIntegrallyClosed A₁]
    [Algebra A₂ A₁] [Module.Finite A₂ A₁] [FaithfulSMul A₂ A₁]
    {G : Type} [Group G] [Fintype G] [MulSemiringAction G A₁] [SMulCommClass G A₂ A₁] [FaithfulSMul G A₁]
    [Algebra.IsInvariant A₂ A₁ G]
    (y : Ideal A₁) [y.IsMaximal] (𝔭 : Ideal A₂) [𝔭.IsPrime] (h𝔭 : y.comap (algebraMap A₂ A₁) = 𝔭)
    (e : ℕ) (he : 0 < e)
    (hIy : Nat.card ↥(y.inertia G) = e) (hIcyc : IsCyclic ↥(y.inertia G))
    (𝔔₀ : Ideal A₂) [𝔔₀.IsPrime] (h𝔔₀ : 𝔔₀ ≤ 𝔭) (ϖ : A₂)
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [Algebra A₂ O] [IsLocalization.AtPrime O 𝔭]
    (s : O) (hsO : 𝔔₀.map (algebraMap A₂ O) = Ideal.span {s})
    (hmaxO : maximalIdeal O = Ideal.span {algebraMap A₂ O ϖ, s}) (hdimO : ringKrullDim O = 2)
    (heO : IsUnit (e : O))

    (hunr : ∀ (𝔔 : Ideal A₁) [𝔔.IsPrime], 𝔔 ≤ y → 𝔔.height = 1 → 𝔔.comap (algebraMap A₂ A₁) ≠ 𝔔₀ →
      Algebra.IsUnramifiedAt A₂ 𝔔)

    (hsep : ∀ h : 𝔭 ≤ y.comap (algebraMap A₂ A₁),
      letI : Algebra (A₂ ⧸ 𝔭) (A₁ ⧸ y) := Ideal.Quotient.algebraQuotientOfLEComap h
      Algebra.IsSeparable (A₂ ⧸ 𝔭) (A₁ ⧸ y)) :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [Algebra A₁ S] [IsLocalization.AtPrime S y],
      IsDomain (AdicCompletion (maximalIdeal S) S) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S) := by sorry
