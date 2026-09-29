-- Prove2me | solution 1 for groupCohomology.Kummer.exists_pow_eq_iff_forall_kummerCocycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d4d5491d-0026-5d28-9725-cff292f48483

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_of_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

private theorem smul_eq_self_of_pow_eq_one
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup)
    {ζ : Ωˣ} (hζ : ζ ^ p = 1) : σ • ζ = ζ :=
  Units.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
    (hμ _ (by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one])))

theorem solution
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω)
    {p : ℕ} (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    {a : Kˣ} {α : Ωˣ} (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔ ∀ σ : K.fixingSubgroup, kummerCocycle α (σ : Ω ≃ₐ[k] Ω) = 1 := by
  rw [exists_pow_eq_iff_of_fixingSubgroup K hα]
  constructor
  · rintro ⟨ζ, hζ, h⟩ σ
    rw [← h σ, smul_eq_self_of_pow_eq_one K hμ σ.2 hζ, div_self']
  · intro h
    exact ⟨1, one_pow _, fun σ => by rw [smul_one, div_one, h σ]⟩

end S_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one
end P2MW
export P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one (solution)
