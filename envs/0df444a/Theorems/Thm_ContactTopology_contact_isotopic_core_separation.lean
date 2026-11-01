-- Prove2me | Theorems.Thm_ContactTopology_contact_isotopic_core_separation
-- name    : ContactTopology.contact_isotopic_core_separation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T06:02:19.147999+00:00
-- url     : https://prove2.me/theorems/8c710301-567a-4d90-99a9-406d235e882f
-- title:
--   Small contact rotations separate a standard core and its actual neighborhoods from a contactomorphic core
-- statement:
--   Let $F$ be any smooth coorientation-preserving contactomorphism of the standard contact three-sphere which commutes with the antipodal involution. Put $c(u)=(u,0)$ for $u\in S^1$ and $C_F=F(c(S^1))$. For every $\varepsilon>0$, there exist $s\in\mathbb R$ with $|s|<\varepsilon$ and an antipodally equivariant sphere contactomorphism $G$ such that
--   $$G(q,p)=\frac{(q+2sp,p-2sq)}{\sqrt{1+4s^2}},\qquad C_F\cap G(c(S^1))=\varnothing.$$
--   The map $G$ is connected to the identity by a smooth antipodally equivariant contact isotopy. Moreover, there are positive radii $r$ and $\rho$ for which
--   $$F(T_r)\cap G(T_\rho)=\varnothing,\qquad T_t=\{(q,p)\in S^3:|p|^2\le t^2|q|^2\}.$$
--   Thus one can obtain a configuration of disjoint actual cores and disjoint round neighborhoods using an arbitrarily small parameter in an explicit contact family. The result does not assert that both knots are core representatives in one solid torus, or provide the subsequent convex neighborhood movie or core-classification theorem.
-- source:
--   Original coordinate auxiliary lemma for the standard contact sphere, proved in the accompanying Lean submission. The critical-value step uses Mathlib, Mathlib/MeasureTheory/Function/Jacobian.lean, MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero, at revision 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/Jacobian.lean . Context: Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.5. This is a separately proved separation lemma, not a formalization of Proposition 3.5 or a claim of core classification.

import Definitions.Def_ContactTopology_CoreSeparation
open BirkhoffGlobalSection ContactTopology.CoreSeparation Set Function
open scoped ContDiff

theorem ContactTopology.contact_isotopic_core_separation (F : EquivariantSphereContactomorphism)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, ∃ G : EquivariantSphereContactomorphism, |s|<ε ∧
      (∀ y : Phase, G.toFun y=rotation s y) ∧
      Nonempty (EquivariantSphereContactIsotopy G) ∧
      Disjoint (coreSet F) (coreSet G) ∧
      ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ Disjoint
        (F.toFun '' standardTube r) (G.toFun '' standardTube q) := by sorry
