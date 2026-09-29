-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
-- name    : AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/61810206-1afa-5778-a457-64c4beeff2f7
-- title:
--   DVR squares with finite residue field for immediate specialisations
-- statement:
--   Let $C$ be a Noetherian commutative ring such that for every maximal ideal $\mathfrak m \subseteq C$ the quotient $C/\mathfrak m$ is finite, let $X$ be a scheme and let $g : X \to \operatorname{Spec} C$ be a morphism locally of finite type. Let $x$ be a point of $X$ and $t$ a point of $\operatorname{Spec} C$ whose singleton $\{t\}$ is closed, and assume that $g(x)$ specialises to $t$, that $g(x) \neq t$, and that the specialisation is immediate in the sense that every prime ideal $\mathfrak p$ of $C$ with $\mathfrak q \subseteq \mathfrak p \subseteq \mathfrak m$, where $\mathfrak q$ and $\mathfrak m$ are the primes corresponding to $g(x)$ and $t$, equals $\mathfrak q$ or $\mathfrak m$. Then there is a valuative commutative square $S$ over $g$, that is, a valuation ring $S.R$ with fraction field $S.K$ together with morphisms $S.i_1 : \operatorname{Spec} S.K \to X$ and $S.i_2 : \operatorname{Spec} S.R \to \operatorname{Spec} C$ forming a commutative square with $g$ and with $\operatorname{Spec}$ of the inclusion $S.R \to S.K$, such that $S.R$ is a discrete valuation ring, its residue field is finite, the closed point of $\operatorname{Spec} S.R$ is sent by $S.i_2$ to $t$, and the image of the map on points underlying $S.i_1$ is contained in the closure of $\{x\}$.
--
--   This is the existence step in a valuative criterion for universal closedness in the arithmetic setting: it produces lifting data of the restricted shape (discrete valuation ring with finite residue field) for a single immediate specialisation towards a closed point of a Noetherian base with finite residue fields. It is used by [`AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift`](thm.html#AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift), which deduces universal closedness from the existence of lifts against all such squares, and it rests on the Krull–Akizuki type statement [`IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField`](thm.html#IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
    {C : Type u} [CommRing C] [IsNoetherianRing C] (hfin : ∀ (m : Ideal C) [m.IsMaximal], Finite (C ⧸ m))
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType g]
    (x : X) (t : ↥(Spec (CommRingCat.of C))) (ht : IsClosed ({t} : Set ↥(Spec (CommRingCat.of C))))
    (hxt : g.base x ⤳ t) (hne : g.base x ≠ t)
    (hcov : ∀ p : Ideal C, p.IsPrime → (g.base x).asIdeal ≤ p → p ≤ t.asIdeal → p = (g.base x).asIdeal ∨ p = t.asIdeal) :
    ∃ S : ValuativeCommSq g, IsDiscreteValuationRing S.R ∧ Finite (IsLocalRing.ResidueField S.R) ∧
      S.i₂.base (IsLocalRing.closedPoint S.R) = t ∧ Set.range S.i₁.base ⊆ closure {x} := by sorry
