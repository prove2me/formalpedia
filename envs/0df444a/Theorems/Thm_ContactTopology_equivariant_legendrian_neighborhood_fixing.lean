-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_neighborhood_fixing
-- name    : ContactTopology.equivariant_legendrian_neighborhood_fixing
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:40:17.511558+00:00
-- url     : https://prove2.me/theorems/955a8d37-7521-463b-9dae-8f15d0555eac
-- title:
--   Equivariant Legendrian neighborhood fixing on the standard sphere
-- statement:
--   Let $F$ be a coorientation-preserving contactomorphism of the standard three-sphere commuting with the antipodal involution. Suppose it fixes the real Legendrian circle pointwise:
--   $$F(\cos(2\pi x),\sin(2\pi x),0,0)=(\cos(2\pi x),\sin(2\pi x),0,0)\quad(x\in\mathbb R).$$
--   There is another equivariant sphere contactomorphism $C$, joined to the identity by a smooth equivariant contact isotopy, and an ambient open set $O\subset\mathbb R^4$ containing that circle, such that
--   $$C(F(y))=y\qquad(y\in O\cap S^3).$$
--
--   Thus the map fixing the circle can be corrected through an ambient equivariant contact isotopy so that it fixes a whole open sphere neighborhood. This is the standard-sphere, antipodally equivariant form of the Legendrian neighborhood-fixing step. It does not assert that an arbitrary contactomorphism is isotopic to the identity: the core-fixing hypothesis is essential to this local statement.
-- source:
--   Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, Lemma 2.7(2), printed pp. 10–12, equations (2)–(8), https://arxiv.org/abs/2207.03590v2 . Standard-sphere antipodally equivariant specialization, obtained by explicit covering coordinates, compact equivariant Hamiltonian extension and integration. Contact-isotopy extension: Geiges, Contact geometry, arXiv:math/0307242v2, Theorem 2.42 and proof, pp. 34–36. The conclusion is an actual open sphere neighborhood, not solely a coordinate deformation.

import Definitions.Def_BirkhoffGlobalSection_SphereContact

theorem ContactTopology.equivariant_legendrian_neighborhood_fixing (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ,
      F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
        ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0]) :
    ∃ C : BirkhoffGlobalSection.EquivariantSphereContactomorphism,
      Nonempty (BirkhoffGlobalSection.EquivariantSphereContactIsotopy C) ∧
      ∃ O : Set BirkhoffGlobalSection.Phase, IsOpen O ∧
        (∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O) ∧
        ∀ y ∈ O ∩ BirkhoffGlobalSection.unitThreeSphere, C.toFun (F.toFun y) = y := by sorry
