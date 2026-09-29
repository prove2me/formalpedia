-- Prove2me | solution 1 for groupCohomology.mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ba4b0509-2351-5e4f-bcfb-84861f4c2a42

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Theorems.Thm_groupCohomology_exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2

set_option autoImplicit false

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "cocycles₂_map_one_fst cocycles₂ d₁₂_hom_apply coboundaries₂ map cocycles₂_map_one_snd π IsMulCocycle₁ levelCoboundaries₂ mem_levelCoboundaries₂_iff unitsInflate₁ unitsInflate₂ exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup"
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

set_option maxHeartbeats 3200000 in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ}
    (hf : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (h : unitsInflate₂ L f ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)) :
    f ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits K L) := by

  have hπsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hπS : ∀ {s : Ω ≃ₐ[K] Ω}, s ∈ L.fixingSubgroup → AlgEquiv.restrictNormalHom L s = 1 :=
    fun {s} hs => (restrictNormalHom_eq_one_iff L s).2 hs
  have hSπ : ∀ {s : Ω ≃ₐ[K] Ω}, AlgEquiv.restrictNormalHom L s = 1 → s ∈ L.fixingSubgroup :=
    fun {s} hs => (restrictNormalHom_eq_one_iff L s).1 hs

  obtain ⟨c, ⟨F₀, hF₀, hclc⟩, hdc⟩ := (mem_levelCoboundaries₂_iff r (Rep.ofAlgebraAutOnUnits K Ω) _).1 h
  have hdc' : ∀ g h' : Ω ≃ₐ[K] Ω, (Rep.ofAlgebraAutOnUnits K Ω).ρ g (c h') - c (g * h') + c g
      = ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h')) := by
    intro g h'
    have e := congrFun hdc (g, h')
    rw [d₁₂_hom_apply] at e
    exact e
  clear hdc h

  obtain ⟨E, hE, hEF⟩ := hopen F₀ hF₀
  have hcE : ∀ (g s : Ω ≃ₐ[K] Ω), s ∈ E.fixingSubgroup → c (g * s) = c g :=
    fun g s hs => hclc g s (hEF s hs)
  clear hclc hEF

  have hf1 : ∀ q : L ≃ₐ[K] L, f (1, q) = f (1, 1) := fun q =>
    cocycles₂_map_one_fst (A := Rep.ofAlgebraAutOnUnits K L) ⟨f, hf⟩ q
  have hf2 : ∀ q : L ≃ₐ[K] L, f (q, 1) = (Rep.ofAlgebraAutOnUnits K L).ρ q (f (1, 1)) := fun q =>
    cocycles₂_map_one_snd (A := Rep.ofAlgebraAutOnUnits K L) ⟨f, hf⟩ q
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Rep.ofAlgebraAutOnUnits K Ω, a₀ = ιA L (f (1, 1)) := ⟨_, rfl⟩
  have F1 : ∀ s h' : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup →
      ιA L (f (AlgEquiv.restrictNormalHom L s, AlgEquiv.restrictNormalHom L h')) = a₀ := by
    intro s h' hs; rw [hπS hs, hf1, ha₀]
  have F2 : ∀ g s : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup →
      ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L s))
        = (Rep.ofAlgebraAutOnUnits K Ω).ρ g a₀ := by
    intro g s hs; rw [hπS hs, hf2, ιA_ρ, ha₀]
  have F3 : ∀ s : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup → (Rep.ofAlgebraAutOnUnits K Ω).ρ s a₀ = a₀ := by
    intro s hs; rw [ha₀, ← ιA_ρ, hπS hs, map_one, Module.End.one_apply]

  have hcS' : ∀ s t : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup → t ∈ L.fixingSubgroup →
      c (s * t) - a₀ = (Rep.ofAlgebraAutOnUnits K Ω).ρ s (c t - a₀) + (c s - a₀) := by
    intro s t hs ht
    have e := hdc' s t
    rw [F1 s t hs] at e
    have e' : c (s * t) = (Rep.ofAlgebraAutOnUnits K Ω).ρ s (c t) + c s - a₀ := by rw [← e]; abel
    rw [e', map_sub, F3 s hs]
    abel
  obtain ⟨c', hc'def⟩ : ∃ c' : L.fixingSubgroup → Ωˣ,
      ∀ s, c' s = Additive.toMul (α := Ωˣ) (c s - a₀) := ⟨_, fun _ => rfl⟩
  have hc' : IsMulCocycle₁ c' := by
    intro s t
    rw [hc'def, hc'def, hc'def, Subgroup.coe_mul, hcS' s t s.2 t.2]
    rfl
  have hc'lc : ∃ L' : IntermediateField K Ω, FiniteDimensional K L' ∧
      ∀ σ τ : L.fixingSubgroup, (τ : Ω ≃ₐ[K] Ω) ∈ L'.fixingSubgroup → c' (σ * τ) = c' σ :=
    ⟨E, hE, fun σ τ hτ => by rw [hc'def, hc'def, Subgroup.coe_mul, hcE _ _ hτ]⟩

  obtain ⟨α, hα⟩ := exists_eq_smul_div_of_isMulCocycle1_fixingSubgroup (k := K) L hc' hc'lc
  obtain ⟨ā, hā⟩ : ∃ ā : Rep.ofAlgebraAutOnUnits K Ω, Additive.toMul (α := Ωˣ) ā = α := ⟨Additive.ofMul α, rfl⟩
  have hcS : ∀ s : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup →
      c s = a₀ + ((Rep.ofAlgebraAutOnUnits K Ω).ρ s ā - ā) := by
    intro s hs
    have e' := hα ⟨s, hs⟩
    rw [hc'def, ← hā] at e'
    have e : c s - a₀ = (Rep.ofAlgebraAutOnUnits K Ω).ρ s ā - ā :=
      (Additive.toMul (α := Ωˣ)).injective e'
    rw [← e]; abel
  clear hα hc'lc hc' hc'def c' hcS' hā

  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω,
      ∀ g, c₁ g = c g - ((Rep.ofAlgebraAutOnUnits K Ω).ρ g ā - ā) := ⟨_, fun _ => rfl⟩
  have hd1 : ∀ g h' : Ω ≃ₐ[K] Ω, (Rep.ofAlgebraAutOnUnits K Ω).ρ g (c₁ h') - c₁ (g * h') + c₁ g
      = ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h')) := by
    intro g h'
    rw [← hdc' g h', hc₁, hc₁, hc₁, map_sub, map_sub, map_mul, Module.End.mul_apply]
    abel
  have hc1S : ∀ s : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup → c₁ s = a₀ := by
    intro s hs; rw [hc₁, hcS s hs]; abel
  clear hcS hdc'

  have h6 : ∀ g s : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup → c₁ (g * s) = c₁ g := by
    intro g s hs
    have e := hd1 g s
    rw [F2 g s hs, hc1S s hs] at e
    calc c₁ (g * s) = (Rep.ofAlgebraAutOnUnits K Ω).ρ g a₀ + c₁ g
          - ((Rep.ofAlgebraAutOnUnits K Ω).ρ g a₀ - c₁ (g * s) + c₁ g) := by abel
      _ = c₁ g := by rw [e]; abel

  have h7 : ∀ s g : Ω ≃ₐ[K] Ω, s ∈ L.fixingSubgroup → (Rep.ofAlgebraAutOnUnits K Ω).ρ s (c₁ g) = c₁ g := by
    intro s g hs
    have e := hd1 s g
    have hconj : c₁ (s * g) = c₁ g := by
      have hmem : g⁻¹ * s * g ∈ L.fixingSubgroup :=
        hSπ (by rw [map_mul, map_mul, map_inv, hπS hs, mul_one, inv_mul_cancel])
      rw [show s * g = g * (g⁻¹ * s * g) by rw [mul_assoc, mul_inv_cancel_left], h6 g _ hmem]
    rw [F1 s g hs, hc1S s hs, hconj] at e
    calc (Rep.ofAlgebraAutOnUnits K Ω).ρ s (c₁ g)
        = ((Rep.ofAlgebraAutOnUnits K Ω).ρ s (c₁ g) - c₁ g + a₀) + c₁ g - a₀ := by abel
      _ = c₁ g := by rw [e]; abel

  have h8 : ∀ g : Ω ≃ₐ[K] Ω, ∃ b : Rep.ofAlgebraAutOnUnits K L, ιA L b = c₁ g := by
    intro g
    have hv : ((Additive.toMul (α := Ωˣ) (c₁ g) : Ωˣ) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro s hs
      exact congrArg (fun a : Rep.ofAlgebraAutOnUnits K Ω => ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)) (h7 s g hs)
    have hne : ((Additive.toMul (α := Ωˣ) (c₁ g) : Ωˣ) : Ω) ≠ 0 := (Additive.toMul (α := Ωˣ) (c₁ g)).ne_zero
    have hne' : (⟨_, hv⟩ : L) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
    exact ⟨(Additive.ofMul (Units.mk0 (⟨_, hv⟩ : L) hne') : Additive (L)ˣ), ext_Ω rfl⟩
  choose xt hxt using h8

  obtain ⟨x, hxdef⟩ : ∃ x : (L ≃ₐ[K] L) → Rep.ofAlgebraAutOnUnits K L,
      ∀ q, x q = xt (Function.surjInv hπsurj q) := ⟨_, fun _ => rfl⟩
  have hx : ∀ g : Ω ≃ₐ[K] Ω, ιA L (x (AlgEquiv.restrictNormalHom L g)) = c₁ g := by
    intro g
    rw [hxdef, hxt]
    have hmem : g⁻¹ * Function.surjInv hπsurj (AlgEquiv.restrictNormalHom L g) ∈ L.fixingSubgroup :=
      hSπ (by rw [map_mul, map_inv, Function.surjInv_eq hπsurj, inv_mul_cancel])
    have e := h6 g _ hmem
    rwa [mul_inv_cancel_left] at e

  refine ⟨x, ?_⟩
  funext ⟨q, q'⟩
  obtain ⟨g, rfl⟩ := hπsurj q
  obtain ⟨h', rfl⟩ := hπsurj q'
  apply ιA_injective L
  rw [d₁₂_hom_apply]
  dsimp only
  rw [map_add, map_sub, ιA_ρ, ← map_mul, hx, hx, hx]
  exact hd1 g h'

end S_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 (solution)
