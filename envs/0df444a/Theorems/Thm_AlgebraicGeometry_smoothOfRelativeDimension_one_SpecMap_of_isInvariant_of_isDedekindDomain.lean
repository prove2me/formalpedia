-- Prove2me | Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
-- name    : AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/2cc98da0-18a2-5fea-a888-d6dd42081865
-- title:
--   Invariants of a smooth relative curve over a Dedekind base
-- statement:
--   Let $B$ be a Dedekind domain, and let $S$ and $A$ be commutative rings with $B$-algebra structures and an $S$-algebra structure on $A$ forming a scalar tower $B \to S \to A$, the structure map $S \to A$ being injective (`FaithfulSMul S A`). Let $G$ be a finite group acting on $A$ by ring automorphisms, the action commuting with the $B$- and $S$-actions, and assume `Algebra.IsInvariant S A G`, so that the image of $S$ in $A$ is exactly the subring of $G$-fixed elements. Assume further the witness hypothesis `hW`: for every maximal ideal $\mathfrak p$ of $B$ there exist a complete discrete valuation ring $W$ (a domain, complete for the adic topology of its maximal ideal) with algebraically closed residue field, together with a $B$-algebra structure making $W$ flat over $B$ and such that the maximal ideal of $W$ contracts to $\mathfrak p$ along $B \to W$. Finally assume that the morphism $\operatorname{Spec} A \to \operatorname{Spec} B$ induced by $B \to A$ is smooth of relative dimension $1$. Then the morphism $\operatorname{Spec} S \to \operatorname{Spec} B$ induced by $B \to S$ is smooth of relative dimension $1$.
--
--   This is the affine form, over a Dedekind base admitting complete discrete valuation ring witnesses at every closed point, of the statement that the quotient of a smooth relative curve by a finite group action is again a smooth relative curve, with no tameness restriction on the stabilisers; it is the local input for the globalised version [`AlgebraicGeometry.smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain). Such quotient-smoothness statements are what make the coarse moduli schemes of elliptic curves with level structure smooth relative curves over their arithmetic bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
    {B S A : Type} [CommRing B] [IsDedekindDomain B] [CommRing S] [CommRing A]
    [Algebra B S] [Algebra B A] [Algebra S A] [IsScalarTower B S A] [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G B A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    (hW : ∀ 𝔭 : Ideal B, 𝔭.IsMaximal →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
        (_ : Algebra B W), Module.Flat B W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B W) = 𝔭)
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B A)))] :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B S))) := by sorry
