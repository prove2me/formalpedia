-- Prove2me | Theorems.Thm_BQC_finite_subgroup_inj
-- name    : BQC.finite_subgroup_inj
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:26:29.952748+00:00
-- url     : https://prove2.me/theorems/801add4e-864a-414f-b27d-0c68dd751d8e
-- title:
--   The holonomy projection is injective on finite subgroups (Lemma 9)
-- statement:
--   If the finite group K embeds into the crystallographic group Cry, then two elements of K whose images have the same projection to the holonomy group are equal. The kernel of the projection is the integer lattice, which is torsion free, while the difference of the two embedded elements would have finite order inside the lattice. This is Lemma 9 of the source paper: the restriction of the projection to any finite subgroup is an isomorphism onto its image, so every finite subgroup of a crystallographic group embeds isomorphically into its holonomy group.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Section 2 (Lemma 9).

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor

namespace BQC

/-!  Milestone 1 (Lemma 9): the projection of a crystallographic group to its
holonomy group is injective on finite subgroups. If the finite group K embeds
into the crystallographic group Cry, then two elements of K with the same
projection are equal. The proof observes that the kernel of the projection is
the integer lattice, which is torsion free, while a nonzero element of the
difference would have finite order inside the lattice. -/
theorem finite_subgroup_inj {d : Nat} {Cry Ph : Type*} [Group Cry] [Group Ph] [Fintype Ph]
    (W : CryWorld d Cry Ph) {K : Type} [Group K] [Fintype K] (f : K →* Cry)
    (finj : ∀ x y : K, f x = f y → x = y) (x y : K)
    (hxy : W.proj (f x) = W.proj (f y)) : x = y := by sorry

end BQC
