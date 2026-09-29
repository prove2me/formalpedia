-- Prove2me | solution 1 for groupCohomology.Kummer.kummerCocycle_pow_eq_one_of_mem_fixingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2657ca6c-37a4-502c-8de0-3f7298b338cd

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_kummerCocycle_pow_eq_one_of_mem_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    {a : K} {α : Ωˣ} (hα : algebraMap K Ω a = (α : Ω) ^ p)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    kummerCocycle α σ ^ p = 1 := by
  have hfix : σ (algebraMap K Ω a) = algebraMap K Ω a :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ a.2
  ext
  rw [Units.val_pow_eq_pow_val, kummerCocycle_apply, Units.val_div_eq_div_val, val_smul_units,
    div_pow, ← map_pow, ← hα, hfix, Units.val_one, div_self]
  rw [hα]; exact pow_ne_zero _ α.ne_zero

end S_groupCohomology_Kummer_kummerCocycle_pow_eq_one_of_mem_fixingSubgroup
end P2MW
export P2MW.S_groupCohomology_Kummer_kummerCocycle_pow_eq_one_of_mem_fixingSubgroup (solution)
