-- Prove2me | solution 1 for groupCohomology.unitsInflate2_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/6ca5bbd6-ae98-59a7-a2f9-59857ae73de9

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_unitsInflate2_mem_levelCoboundaries2

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_unitsInflate2_mem_levelCoboundaries2.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂_hom_apply coboundaries₂ map levelCoboundaries₂ mem_levelCoboundaries₂_iff unitsInflate₁ unitsInflate₂"
p2m_open "groupCohomology"

section GIhelpers
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω)

private noncomputable def ιA : (Rep.ofAlgebraAutOnUnits K L) →+ (Rep.ofAlgebraAutOnUnits K Ω) where
  toFun b := (Additive.ofMul (Units.map (algebraMap L Ω).toMonoidHom (Additive.toMul (α := (L)ˣ) b)) :
    Additive Ωˣ)
  map_zero' := congrArg Additive.ofMul (map_one (Units.map (algebraMap L Ω).toMonoidHom))
  map_add' b b' := congrArg Additive.ofMul
    (map_mul (Units.map (algebraMap L Ω).toMonoidHom) (Additive.toMul (α := (L)ˣ) b)
      (Additive.toMul (α := (L)ˣ) b'))

private lemma coe_ιA (b : Rep.ofAlgebraAutOnUnits K L) :
    ((Additive.toMul (α := Ωˣ) (ιA L b) : Ωˣ) : Ω) = algebraMap L Ω ((Additive.toMul (α := (L)ˣ) b : (L)ˣ) : L) :=
  rfl

private lemma ιA_injective : Function.Injective (ιA L) := by
  intro b b' h
  have h' := congrArg (fun a : Rep.ofAlgebraAutOnUnits K Ω => ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)) h
  simp only [coe_ιA] at h'
  exact (Additive.toMul (α := (L)ˣ)).injective (Units.ext ((algebraMap L Ω).injective h'))

private lemma coe_ρΩ (g : Ω ≃ₐ[K] Ω) (a : Rep.ofAlgebraAutOnUnits K Ω) :
    ((Additive.toMul (α := Ωˣ) ((Rep.ofAlgebraAutOnUnits K Ω).ρ g a) : Ωˣ) : Ω)
      = g ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω) := rfl

private lemma ext_Ω {a a' : Rep.ofAlgebraAutOnUnits K Ω}
    (h : ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω) = ((Additive.toMul (α := Ωˣ) a' : Ωˣ) : Ω)) : a = a' :=
  (Additive.toMul (α := Ωˣ)).injective (Units.ext h)

variable [Normal K L]

private lemma unitsInflate₂_eq (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (g h : Ω ≃ₐ[K] Ω) :
    unitsInflate₂ L f (g, h) = ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h)) := rfl

private lemma unitsInflate₁_eq (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (g : Ω ≃ₐ[K] Ω) :
    unitsInflate₁ L c g = ιA L (c (AlgEquiv.restrictNormalHom L g)) := rfl

private lemma ιA_ρ (g : Ω ≃ₐ[K] Ω) (b : Rep.ofAlgebraAutOnUnits K L) :
    ιA L ((Rep.ofAlgebraAutOnUnits K L).ρ (AlgEquiv.restrictNormalHom L g) b)
      = (Rep.ofAlgebraAutOnUnits K Ω).ρ g (ιA L b) :=
  ext_Ω (AlgEquiv.restrictNormal_commutes g L _)

private lemma restrictNormalHom_eq_one_iff (s : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictNormalHom L s = 1 ↔ s ∈ L.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]

end GIhelpers

end groupCohomology

set_option maxHeartbeats 1600000 in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ L.fixingSubgroup)
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits K L)) :
    unitsInflate₂ L f ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by
  obtain ⟨x, rfl⟩ := hf
  obtain ⟨F, hF, hFL⟩ := hL
  refine (mem_levelCoboundaries₂_iff r _ _).2 ⟨unitsInflate₁ L x, ⟨F, hF, fun g s hs => ?_⟩, ?_⟩
  · rw [unitsInflate₁_eq, unitsInflate₁_eq, map_mul, (restrictNormalHom_eq_one_iff L s).2 (hFL s hs), mul_one]
  · funext ⟨g, h⟩
    rw [unitsInflate₂_eq]
    simp only [d₁₂_hom_apply, map_add, map_sub, unitsInflate₁_eq, map_mul, ιA_ρ]

end S_groupCohomology_unitsInflate2_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_unitsInflate2_mem_levelCoboundaries2 (solution)
