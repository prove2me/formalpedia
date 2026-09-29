-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
-- name    : AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/b1ae1620-f8d0-59a4-958d-3360d792e40f
-- title:
--   Morphism from a reduced scheme to a closed point factors through its residue field
-- statement:
--   Let $Z$ and $S$ be schemes with $Z$ reduced, let $g \colon Z \to S$ be a quasi-compact morphism of schemes, and let $s$ be a point of $S$ whose singleton $\{s\}$ is closed in the underlying topological space of $S$. Assume that the image of the continuous map $g$ underlying $g$ on points, i.e. the range of `g.base`, is contained in $\{s\}$. Then there exists a morphism of schemes $t \colon Z \to \operatorname{Spec}(\kappa(s))$, where $\kappa(s)$ is the residue field of $S$ at $s$, such that $t$ followed by the canonical morphism $\operatorname{Spec}(\kappa(s)) \to S$ (Mathlib's `Scheme.fromSpecResidueField`) equals $g$. Only existence of such a factorisation is asserted; no uniqueness claim is made, although the factorisation is in fact unique since the canonical morphism from the residue field is a monomorphism.
--
--   This is the standard statement that a morphism whose set-theoretic image is a single closed point factors through the reduced induced structure on that point, namely through the spectrum of the residue field, provided the source is reduced. It is used in the construction of maps out of fake elliptic curves with extra level structure, where a morphism landing on a single closed point of the base has to be exhibited as a point of that fibre's residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_comp_fromSpecResidueField_eq_of_range_subset_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_comp_fromSpecResidueField_eq_of_range_subset_singleton
    {Z S : Scheme.{u}} [IsReduced Z] (g : Z ⟶ S) [QuasiCompact g]
    (s : S) (hs : IsClosed ({s} : Set S)) (hg : Set.range g.base ⊆ {s}) :
    ∃ t : Z ⟶ Spec (S.residueField s), t ≫ S.fromSpecResidueField s = g := by sorry
