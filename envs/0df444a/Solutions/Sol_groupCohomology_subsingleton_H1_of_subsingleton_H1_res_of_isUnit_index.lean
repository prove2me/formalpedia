-- Prove2me | solution 1 for groupCohomology.subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/85333193-65a8-574b-83e9-88cf59ec6294

import Mathlib
import Theorems.Thm_groupCohomology_injective_H1_restriction_of_isUnit_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]
    [Fintype (G ⧸ S)] (hindex : IsUnit ((Fintype.card (G ⧸ S) : k)))
    (hS : Subsingleton (H1 (Rep.res S.subtype A))) :
    Subsingleton (H1 A) := by
  haveI h₃ : Subsingleton ((H1InfRes A S).X₃ : Type u) := hS
  exact ⟨fun a b => injective_H1_restriction_of_isUnit_index hindex (Subsingleton.elim _ _)⟩

end S_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index
end P2MW
export P2MW.S_groupCohomology_subsingleton_H1_of_subsingleton_H1_res_of_isUnit_index (solution)
