-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_complement_connected
-- name    : ContactTopology.equivariant_legendrian_complement_connected
-- status  : Open
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:48:39.738775+00:00
-- url     : https://prove2.me/theorems/fc466350-c30b-4cbc-82e5-f5fee5cd5eae
-- title:
--   Contact connectedness after fixing a standard Legendrian neighborhood
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere that commutes with the antipodal involution. Suppose there is an open set $O\subset\mathbb R^4$ containing the real Legendrian circle
--   $$c(x)=(\cos(2\pi x),\sin(2\pi x),0,0)$$
--   such that $F(y)=y$ for all $y\in O\cap S^3$. Then $F$ is joined to the identity by a smooth antipodally equivariant contact isotopy:
--   $$F_0=\operatorname{id}_{S^3},\qquad F_1=F.$$
--
--   This is the standard $\mathbb{RP}^3$ complementary-solid-torus step, lifted to its antipodal sphere cover. The neighborhood hypothesis allows a smaller standard Legendrian neighborhood to be chosen on which the map is already the identity. The conclusion is a global isotopy; it does not additionally require every intermediate map to fix that neighborhood.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/abs/2207.03590v2, Section 4, proof of Theorem 1.1 (Claim 1 and p=2 case), printed pp. 32–33. Specializes Theorem 3.1 (universally tight solid torus, convex boundary with two dividing curves, isotopies relative to the boundary) to the complement of a standard Legendrian neighborhood, as applied explicitly in Section 4. The standard-neighborhood/complement identifications, boundary-compatible gluing, smooth collar convention and antipodal lift are part of this specialized statement.

import Definitions.Def_BirkhoffGlobalSection_SphereContact

theorem ContactTopology.equivariant_legendrian_complement_connected
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (hfix : ∃ O : Set BirkhoffGlobalSection.Phase, IsOpen O ∧
      (∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O) ∧
      ∀ y ∈ O ∩ BirkhoffGlobalSection.unitThreeSphere, F.toFun y = y) :
    Nonempty (BirkhoffGlobalSection.EquivariantSphereContactIsotopy F) := by sorry
