-- Prove2me | solution 1 for groupCohomology.Kummer.exists_kummerCocycle_eq_of_isMulCocycle1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c8cc8daf-3307-566e-a964-398064c7d3c7

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f) (hfp : ∀ σ : L ≃ₐ[K] L, f σ ^ p = 1) :
    ∃ (a : Kˣ) (α : Lˣ),
      algebraMap K L (a : K) = (α : L) ^ p ∧ ∀ σ : L ≃ₐ[K] L, f σ = kummerCocycle α σ := by
  obtain ⟨α, hα⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf

  have hfix : ∀ σ : L ≃ₐ[K] L, σ ((α ^ p : Lˣ) : L) = ((α ^ p : Lˣ) : L) := by
    intro σ
    rw [← val_smul_units, smul_units_pow]
    have h1 : (σ • α) ^ p = α ^ p * (f σ) ^ p := by
      rw [← hα σ, div_pow, mul_div_assoc']
      rw [mul_comm, mul_div_assoc, div_self', mul_one]
    rw [h1, hfp σ, mul_one]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed ((α ^ p : Lˣ) : L)).mpr hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (α ^ p).ne_zero (by rw [← hc, map_zero])
  exact ⟨Units.mk0 c hc0, α,
    by rw [Units.val_mk0, hc, Units.val_pow_eq_pow_val],
    fun σ => (hα σ).symm⟩

end S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1
end P2MW
export P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1 (solution)
