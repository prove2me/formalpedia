-- Prove2me | solution 1 for groupCohomology.finite_groupCohomology_succ_of_moduleFinite_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/92cde06a-5275-503e-97f0-2a64dfea37a9

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_card_smul_eq_zero_of_tateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int
p2m_attr_erase "simp" "Rep.coe_tateδneg2_apply"

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology

set_option maxHeartbeats 1600000

private theorem P2mS26K1.moduleFinite_groupCohomology {k G : Type u} [CommRing k] [IsNoetherianRing k] [Group G] [Finite G]
    (L : Rep.{u} k G) [Module.Finite k L] (n : ℕ) : Module.Finite k (groupCohomology L n) := by
  haveI : Module.Finite k ((groupCohomology.inhomogeneousCochains L).X n) := by
    change Module.Finite k ((Fin n → G) → L)
    infer_instance
  haveI : IsNoetherian k ((groupCohomology.inhomogeneousCochains L).X n) := isNoetherian_of_isNoetherianRing_of_finite k _
  haveI : Module.Finite k (groupCohomology.cocycles L n) :=
    Module.Finite.of_injective (groupCohomology.iCocycles L n).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (groupCohomology.π L n).hom
    (fun x => groupCohomology_induction_on x fun y => ⟨y, rfl⟩)

theorem solution {G : Type} [Group G] [Finite G]
    (L : Rep ℤ G) [Module.Finite ℤ L] (n : ℕ) :
    Finite (groupCohomology L (n + 1)) := by
  classical
  haveI := Fintype.ofFinite G
  have hL : Module.Finite ℤ L := ‹_›
  haveI hH : Module.Finite ℤ (groupCohomology L (n + 1)) :=
    @P2mS26K1.moduleFinite_groupCohomology ℤ G _ _ _ _ L (by convert hL <;> first | rfl | exact Subsingleton.elim _ _) (n + 1)

  refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(Fintype.card G : ℤ), mem_nonZeroDivisors_of_ne_zero
    (by exact_mod_cast Fintype.card_ne_zero)⟩, ?_⟩
  exact Rep.card_smul_eq_zero_of_tateCohomology L ((n + 1 : ℕ) : ℤ) x

end S_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int
end P2MW
export P2MW.S_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int (solution)
