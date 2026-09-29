-- Prove2me | Theorems.Thm_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
-- name    : Algebra.IsInvariant.isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/dcfc27f8-5315-5f70-9751-d3d683aa5808
-- title:
--   Local rings of invariants of a one-dimensional regular ring
-- statement:
--   Let $S$ and $A$ be commutative rings with $A$ an $S$-algebra whose structure map is injective (`FaithfulSMul S A`), and suppose both $S$ and $A$ are Noetherian. Let $G$ be a finite group acting on $A$ by ring automorphisms, the action commuting with the $S$-action on $A$, and assume `Algebra.IsInvariant S A G`, i.e. every element of $A$ fixed by all of $G$ lies in the image of $S$. Assume that for every maximal ideal $P$ of $A$ the localisation $A_P$ (`Localization.AtPrime P`) is an integral domain and, as such, a discrete valuation ring; in Lean this is phrased as the existence of an `IsDomain` instance together with `IsDiscreteValuationRing`, since the latter class presupposes the former. Then for every maximal ideal $q$ of $S$ the localisation $S_q$ is likewise an integral domain and a discrete valuation ring, again asserted as the existence of an `IsDomain` instance on `Localization.AtPrime q` together with `IsDiscreteValuationRing` for it.
--
--   This is the local statement that the ring of invariants of a finite group acting on a Noetherian ring all of whose local rings at maximal ideals are discrete valuation rings again has discrete valuation rings as its local rings at maximal ideals — a regularity-descent step in dimension one. It is used in the proof of [`AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAlgClosed), where smoothness of relative dimension one is deduced for a quotient by a finite group action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.IsInvariant.isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
    {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] [FaithfulSMul S A]
    [IsNoetherianRing S] [IsNoetherianRing A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G S A] [Algebra.IsInvariant S A G]
    (hA : ∀ (P : Ideal A) (_ : P.IsMaximal),
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P))
    (q : Ideal S) [q.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime q), IsDiscreteValuationRing (Localization.AtPrime q) := by sorry
