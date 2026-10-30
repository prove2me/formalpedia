-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_alignment
-- name    : ContactTopology.equivariant_legendrian_core_alignment
-- status  : Open
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:48:37.634041+00:00
-- url     : https://prove2.me/theorems/7944b556-e42c-44d2-a330-4211e4263a85
-- title:
--   Equivariant contact alignment of the standard Legendrian core
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere that commutes with the antipodal involution. Write
--   $$c(x)=(\cos(2\pi x),\sin(2\pi x),0,0)\qquad(x\in\mathbb R)$$
--   for the real Legendrian circle with its fixed parametrization. There exists an equivariant contactomorphism $A$, joined to the identity by a smooth equivariant contact isotopy, such that
--   $$A(F(c(x)))=c(x)\qquad\text{for every }x\in\mathbb R.$$
--
--   This is the sphere-cover form of the core-alignment step for standard $\mathbb{RP}^3=L(2,1)$. It supplies a correction after which the original map fixes the standard core pointwise, allowing a Legendrian neighborhood-fixing theorem to be applied. The endpoint includes the parametrization and the possible antipodal lift discrepancy; equality of knot images alone is weaker than this statement.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Section 4, proof of Theorem 1.1 (Claim 1 and p=2 case), printed pp. 32–33. Uses Proposition 3.5 (or Theorem 1.5), smooth mapping-class triviality for L(2,1) from Theorem 2.11, and the contact isotopy extension theorem cited there (Geiges, An Introduction to Contact Topology, Theorem 2.6.2). Antipodal sphere-cover specialization with parametrization and deck corrections included.

import Definitions.Def_BirkhoffGlobalSection_SphereContact

theorem ContactTopology.equivariant_legendrian_core_alignment
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism) :
    ∃ A : BirkhoffGlobalSection.EquivariantSphereContactomorphism,
      Nonempty (BirkhoffGlobalSection.EquivariantSphereContactIsotopy A) ∧
      ∀ x : ℝ, A.toFun (F.toFun
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] := by sorry
