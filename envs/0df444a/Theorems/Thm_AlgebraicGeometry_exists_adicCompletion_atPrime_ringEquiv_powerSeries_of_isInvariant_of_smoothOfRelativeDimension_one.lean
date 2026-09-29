-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/d7b15adb-9320-5b1e-a716-c83e53ff6046
-- title:
--   Completed local rings of invariant subrings of smooth relative curves
-- statement:
--   Let $W$ be a complete discrete valuation domain (complete for the adic topology of its maximal ideal) whose residue field is algebraically closed. Let $S$ and $A$ be commutative rings with $W$-algebra and $S$-algebra structures forming a scalar tower over $W$, with the action of $S$ on $A$ faithful. Let $G$ be a finite group acting on $A$ by ring automorphisms commuting with the scalar actions of $W$ and of $S$, and assume that $S \to A$ realises the invariants, in the sense of `Algebra.IsInvariant S A G`: every $G$-fixed element of $A$ lies in the image of $S$. Assume further that the morphism of schemes $\operatorname{Spec} A \to \operatorname{Spec} W$ induced by $W \to A$ is smooth of relative dimension $1$. Then for every maximal ideal $\mathfrak q$ of $S$ lying over the maximal ideal of $W$ there exists a ring isomorphism $e$ from the adic completion of the localisation $S_{\mathfrak q}$ with respect to its maximal ideal onto the formal power series ring $W[[X]]$, such that for every $a \in W$ the element $e$ assigns to the image of $a$ under $W \to S \to S_{\mathfrak q} \to \widehat{S_{\mathfrak q}}$ is the constant power series $a$. No hypothesis restricts the order of $G$ or of the stabilisers relative to the residue characteristic.
--
--   This is the local form of the statement that a quotient of a smooth relative curve over a complete discrete valuation ring by a finite group action is again smooth of relative dimension one, allowing wildly ramified points, as in the treatment of coarse moduli of elliptic curves by Katz–Mazur and by Deligne–Rapoport. It is cited by [`AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isAdicComplete_of_isAlgClosed_residueField), which deduces smoothness of $\operatorname{Spec} S \to \operatorname{Spec} W$ from the identification of the completed local rings with $W[[X]]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.exists_adicCompletion_atPrime_ringEquiv_powerSeries_of_isInvariant_of_smoothOfRelativeDimension_one
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [IsAlgClosed (ResidueField W)]
    {S A : Type} [CommRing S] [CommRing A] [Algebra W S] [Algebra W A] [Algebra S A] [IsScalarTower W S A]
    [FaithfulSMul S A]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G W A] [SMulCommClass G S A]
    [Algebra.IsInvariant S A G]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap W A)))]
    (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)] :
    ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔮)) (Localization.AtPrime 𝔮) ≃+* PowerSeries W,
      ∀ a : W, e (algebraMap (Localization.AtPrime 𝔮) _
          (algebraMap S (Localization.AtPrime 𝔮) (algebraMap W S a))) = PowerSeries.C a := by sorry
