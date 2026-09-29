-- Prove2me | solution 1 for groupCohomology.Kummer.exists_pow_eq_iff_exists_rootOfUnity_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7cbe488a-b8b7-5b46-9853-4508a9e864eb

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

private theorem mem_range_algebraMap_of_forall_smul_eq
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L] {x : L}
    (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) : x ∈ Set.range (algebraMap K L) := by
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ => hx σ
  rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hmem
  exact hmem

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Lˣ, ζ ^ p = 1 ∧ ∀ σ : L ≃ₐ[K] L, σ • ζ / ζ = kummerCocycle α σ := by
  constructor
  · rintro ⟨b, rfl⟩
    set β : Lˣ := Units.map (algebraMap K L : K →* L) b with hβ_def
    have hβval : (β : L) = algebraMap K L (b : K) := rfl
    have hβrange : (β : L) ∈ Set.range (algebraMap K L) := ⟨b, hβval.symm⟩
    have hβp : β ^ p = α ^ p := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hβval, ← map_pow, ← hα,
        Units.val_pow_eq_pow_val]
    refine ⟨α / β, ?_, fun σ => ?_⟩
    · rw [div_pow, hβp, div_self']
    · rw [smul_units_div, smul_units_eq_self_of_mem_range σ hβrange, kummerCocycle_apply,
        div_div_div_comm, div_self', div_one]
  · rintro ⟨ζ, hζp, hζ⟩
    have hfix : ∀ σ : L ≃ₐ[K] L, σ ((α / ζ : Lˣ) : L) = ((α / ζ : Lˣ) : L) := by
      intro σ
      rw [← val_smul_units, smul_units_div]
      congr 1
      rw [div_eq_div_iff_mul_eq_mul]
      have h1 : σ • ζ * α = σ • α * ζ := div_eq_div_iff_mul_eq_mul.mp (hζ σ)
      rw [mul_comm (α : Lˣ) (σ • ζ)]
      exact h1.symm
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_forall_smul_eq (hfix)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (α / ζ).ne_zero (by rw [← hc, map_zero])
    refine ⟨Units.mk0 c hc0, ?_⟩
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply (algebraMap K L).injective
    rw [map_pow, hc, hα, Units.val_div_eq_div_val, div_pow, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, hζp, Units.val_one, div_one]

end S_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary
end P2MW
export P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_exists_rootOfUnity_coboundary (solution)
