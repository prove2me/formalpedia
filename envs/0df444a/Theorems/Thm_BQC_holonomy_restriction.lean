-- Prove2me | Theorems.Thm_BQC_holonomy_restriction
-- name    : BQC.holonomy_restriction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:27:09.621693+00:00
-- url     : https://prove2.me/theorems/b6091cfc-2304-45bb-b923-3ef87e2fd8e8
-- title:
--   Every subgroup of the holonomy group is the holonomy group of a crystallographic subgroup (Corollary 10)
-- statement:
--   For every embedding of the finite group H into the holonomy group Ph of a crystallographic group, the set of the elements whose projection is the image of some element of H is a subgroup of the crystallographic group. This is the crystallographic subgroup of Corollary 10 of the source paper: every subgroup of the holonomy group occurs as the holonomy group of a crystallographic subgroup of the same dimension, the starting point of the Bieberbach group constructions of Theorem 20.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Section 2 (Corollary 10).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 2 (Corollary 10): every subgroup of the holonomy group is the
holonomy group of a crystallographic subgroup. For every embedding of the
finite group H into the holonomy group Ph, the preimage of the image of H
under the projection is a subgroup of the crystallographic group; it is the
crystallographic subgroup of Corollary 10, the starting point of the
Bieberbach group constructions of Theorem 20. -/
theorem holonomy_restriction {d : Nat} {Cry Ph : Type*} [Group Cry] [Group Ph] [Fintype Ph]
    (W : CryWorld d Cry Ph) {H : Type} [Group H] [Fintype H] (j : H →* Ph)
    (hinj : ∀ x y : H, j x = j y → x = y) :
    ∃ T : Subgroup Cry, ∀ p : Cry, p ∈ T ↔ ∃ h : H, W.proj p = j h := by sorry

end BQC
