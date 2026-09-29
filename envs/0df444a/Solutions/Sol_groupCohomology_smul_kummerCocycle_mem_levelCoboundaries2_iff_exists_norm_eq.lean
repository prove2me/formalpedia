-- Prove2me | solution 1 for groupCohomology.smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9699609e-b6fc-55a4-802c-c0748233e496

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2π congr cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff π δ H2π_eq_zero_iff IsLevelConstant₁ IsLevelConstant₂ levelCocycles₂ levelCoboundaries₂ continuousH2π continuousH2π_eq_zero_iff cochainsPullPush₂_mem_levelCoboundaries₂ levelCocycles₂Map Kummer.kummerCocycle Kummer.kummerCocycle_apply Kummer.kummerRep Kummer.kummerCocycleRoots Kummer.isMulCocycle₁_kummerCocycleRoots unitsInflate₁ unitsInflate₂ cyclicLog carryFun smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero unitsInflate2_mem_levelCoboundaries2 mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 carryFun_mem_cocycles2 carry_H2pi_eq_zero_iff"
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

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2π congr cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff π δ H2π_eq_zero_iff IsLevelConstant₁ IsLevelConstant₂ levelCocycles₂ levelCoboundaries₂ continuousH2π continuousH2π_eq_zero_iff cochainsPullPush₂_mem_levelCoboundaries₂ levelCocycles₂Map Kummer.kummerCocycle Kummer.kummerCocycle_apply Kummer.kummerRep Kummer.kummerCocycleRoots Kummer.isMulCocycle₁_kummerCocycleRoots unitsInflate₁ unitsInflate₂ cyclicLog carryFun smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero unitsInflate2_mem_levelCoboundaries2 mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 carryFun_mem_cocycles2 carry_H2pi_eq_zero_iff"
p2m_open "groupCohomology"

section T5helpers

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

private theorem exists_cocycles₂_sub_d₁₂' {A : Rep ℤ (Ω ≃ₐ[K] Ω)} (F : cocycles₂ A) (c : (Ω ≃ₐ[K] Ω) → A) :
    ∃ F' : cocycles₂ A, ∀ g h, F' (g, h) = F (g, h) - (A.ρ g (c h) - c (g * h) + c g) :=
  ⟨F - ⟨d₁₂ A c, d₁₂_apply_mem_cocycles₂ c⟩, fun g h => by
    show F (g, h) - d₁₂ A c (g, h) = _
    rw [d₁₂_hom_apply]⟩

private theorem cocycles₂_identity' {A : Rep ℤ (Ω ≃ₐ[K] Ω)} (F : cocycles₂ A) (g h j : Ω ≃ₐ[K] Ω) :
    F (g * h, j) + F (g, h) = A.ρ g (F (h, j)) + F (g, h * j) :=
  (mem_cocycles₂_iff (⇑F)).1 F.2 g h j

private theorem exists_forall_mem_fixingSubgroup_ρ_eq [Algebra.IsAlgebraic K Ω] (a : Rep.ofAlgebraAutOnUnits K Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → (Rep.ofAlgebraAutOnUnits K Ω).ρ σ a = a := by
  refine ⟨IntermediateField.adjoin K {((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _), fun σ hσ => ext_Ω ?_⟩
  rw [coe_ρΩ]
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ _
    (IntermediateField.subset_adjoin K _ (Set.mem_singleton _))

private theorem conj_mem_fixingSubgroup_of_mem_map (E : IntermediateField K Ω) (g u : Ω ≃ₐ[K] Ω)
    (hu : u ∈ (E.map (g : Ω →ₐ[K] Ω)).fixingSubgroup) : g⁻¹ * u * g ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
  intro x hx
  have hgx : g x ∈ E.map (g : Ω →ₐ[K] Ω) := ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu _ hgx, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

private theorem finiteDimensional_map (E : IntermediateField K Ω) [FiniteDimensional K E] (g : Ω ≃ₐ[K] Ω) :
    FiniteDimensional K (E.map (g : Ω →ₐ[K] Ω)) :=
  LinearEquiv.finiteDimensional (IntermediateField.intermediateFieldMap g E).toLinearEquiv

end T5helpers

end groupCohomology

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2π congr cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff π δ H2π_eq_zero_iff IsLevelConstant₁ IsLevelConstant₂ levelCocycles₂ levelCoboundaries₂ continuousH2π continuousH2π_eq_zero_iff cochainsPullPush₂_mem_levelCoboundaries₂ levelCocycles₂Map Kummer.kummerCocycle Kummer.kummerCocycle_apply Kummer.kummerRep Kummer.kummerCocycleRoots Kummer.isMulCocycle₁_kummerCocycleRoots unitsInflate₁ unitsInflate₂ cyclicLog carryFun smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero unitsInflate2_mem_levelCoboundaries2 mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 carryFun_mem_cocycles2 carry_H2pi_eq_zero_iff"
p2m_open "groupCohomology"

private noncomputable def valHomL {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] :
    (Rep.ofAlgebraAutOnUnits K L) →+ Additive L where
  toFun x := Additive.ofMul (((Additive.toMul (α := Lˣ) x) : Lˣ) : L)
  map_zero' := rfl
  map_add' x y := congrArg Additive.ofMul (Units.val_mul (Additive.toMul (α := Lˣ) x) (Additive.toMul (α := Lˣ) y))

private lemma toMul_valHomL {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (x : Rep.ofAlgebraAutOnUnits K L) :
    Additive.toMul (valHomL x) = ((Additive.toMul (α := Lˣ) x : Lˣ) : L) := rfl

private lemma toMul_valHomL_ρ {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Rep.ofAlgebraAutOnUnits K L) :
    Additive.toMul (valHomL ((Rep.ofAlgebraAutOnUnits K L).ρ σ x)) = σ ((Additive.toMul (α := Lˣ) x : Lˣ) : L) := rfl

private theorem key_cocycle {V : Type*} [AddCommGroup V] (Xu Yt : V) (cσ cτ cστ p δ : ℤ)
    (hδ : cσ + cτ - cστ = p * δ) (hp : p • Xu = 0) :
    cστ • Xu + cσ • Yt = cτ • Xu + (cσ • Xu + cσ • Yt) := by
  have h : cστ = cσ + cτ - p * δ := by linarith
  subst h
  have : (p * δ) • Xu = 0 := by rw [mul_comm, mul_smul, hp, smul_zero]
  rw [sub_smul, this, sub_zero]
  module

end groupCohomology

set_option maxHeartbeats 3200000 in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ℤ) (hχlc : IsLevelConstant₁ r χ)
    (hχ : ∀ σ τ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (Kχ : IntermediateField K Ω) [FiniteDimensional K Kχ]
    (hKχ : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ Kχ.fixingSubgroup ↔ (p : ℤ) ∣ χ σ)
    (hsurj : ∃ σ : Ω ≃ₐ[K] Ω, ¬ (p : ℤ) ∣ χ σ)
    (a : Kˣ) (α : Ωˣ) (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
      ∈ levelCoboundaries₂ r (Kummer.kummerRep K Ω p)
    ↔ ∃ w : Kχ, Algebra.norm K w = (a : K) := by
  classical
  haveI : Algebra.IsAlgebraic K Ω := inferInstance

  obtain ⟨χb, hχb⟩ : ∃ χb : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod p),
      ∀ σ, χb σ = Multiplicative.ofAdd ((χ σ : ℤ) : ZMod p) := by
    refine ⟨{ toFun := fun σ => Multiplicative.ofAdd ((χ σ : ℤ) : ZMod p), map_one' := ?_, map_mul' := ?_ }, fun _ => rfl⟩
    · have h := hχ 1 1
      rw [mul_one] at h
      have h0 : ((χ 1 : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using h
      show Multiplicative.ofAdd ((χ 1 : ℤ) : ZMod p) = 1
      rw [h0]; rfl
    · intro σ τ
      show Multiplicative.ofAdd ((χ (σ * τ) : ℤ) : ZMod p)
        = Multiplicative.ofAdd ((χ σ : ℤ) : ZMod p) * Multiplicative.ofAdd ((χ τ : ℤ) : ZMod p)
      rw [← ofAdd_add, ← Int.cast_add]
      congr 1
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      simpa using hχ σ τ
  have hker : ∀ σ, χb σ = 1 ↔ σ ∈ Kχ.fixingSubgroup := by
    intro σ
    rw [hKχ, hχb, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hkerN : χb.ker = Kχ.fixingSubgroup := by
    ext σ; rw [MonoidHom.mem_ker]; exact hker σ
  haveI : Kχ.fixingSubgroup.Normal := by rw [← hkerN]; infer_instance
  haveI : IsGalois K Kχ := (InfiniteGalois.normal_iff_isGalois Kχ).mp inferInstance
  haveI : Normal K Kχ := inferInstance

  have hπker : ∀ σ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom Kχ σ = 1 ↔ σ ∈ Kχ.fixingSubgroup := fun σ => by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
  have hπχ : ∀ σ τ : Ω ≃ₐ[K] Ω, χb σ = χb τ → AlgEquiv.restrictNormalHom Kχ σ = AlgEquiv.restrictNormalHom Kχ τ := by
    intro σ τ h
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hπker, ← hker, map_mul, map_inv, h, inv_mul_cancel]
  have hχπ : ∀ σ τ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom Kχ σ = AlgEquiv.restrictNormalHom Kχ τ → χb σ = χb τ := by
    intro σ τ h
    rw [← inv_mul_eq_one, ← map_inv, ← map_mul, hker, ← hπker, map_mul, map_inv, h, inv_mul_cancel]

  obtain ⟨σ₀, hσ₀⟩ := hsurj
  have hu : ((χ σ₀ : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((k : ZMod p) * ((χ σ₀ : ℤ) : ZMod p)) = 1 :=
    ⟨((χ σ₀ : ℤ) : ZMod p)⁻¹.val, by rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hu]⟩
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : Ω ≃ₐ[K] Ω, χb σ₁ = Multiplicative.ofAdd 1 := by
    refine ⟨σ₀ ^ k, ?_⟩
    rw [map_pow, hχb, ← ofAdd_nsmul, nsmul_eq_mul, hk]
  obtain ⟨s, hsdef⟩ : ∃ s : Kχ ≃ₐ[K] Kχ, s = AlgEquiv.restrictNormalHom Kχ σ₁ := ⟨_, rfl⟩
  have hχbpow : ∀ n : ℕ, χb (σ₁ ^ n) = Multiplicative.ofAdd (n : ZMod p) := fun n => by
    rw [map_pow, hσ₁, ← ofAdd_nsmul, nsmul_one]
  have hπ_of_χb : ∀ (σ : Ω ≃ₐ[K] Ω) (n : ℕ), χb σ = Multiplicative.ofAdd (n : ZMod p) →
      AlgEquiv.restrictNormalHom Kχ σ = s ^ n := by
    intro σ n h
    rw [hsdef, ← map_pow]
    exact hπχ σ _ (h.trans (hχbpow n).symm)
  have hs : ∀ g, g ∈ Subgroup.zpowers s := by
    intro g
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω g
    refine ⟨(((χ σ : ℤ) : ZMod p)).val, ?_⟩
    dsimp only
    rw [zpow_natCast, ← hπ_of_χb σ _ (by rw [hχb, ZMod.natCast_zmod_val])]
  have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s
  have hsχ : ∀ σ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ - (cyclicLog s hs hfin (AlgEquiv.restrictNormalHom Kχ σ) : ℤ) := by
    intro σ
    have e := (finEquivZPowers hfin).apply_symm_apply ⟨AlgEquiv.restrictNormalHom Kχ σ, hs _⟩
    rw [finEquivZPowers_apply] at e
    have e' : s ^ (cyclicLog s hs hfin (AlgEquiv.restrictNormalHom Kχ σ)) = AlgEquiv.restrictNormalHom Kχ σ :=
      congrArg Subtype.val e
    have e'' : AlgEquiv.restrictNormalHom Kχ (σ₁ ^ cyclicLog s hs hfin (AlgEquiv.restrictNormalHom Kχ σ))
        = AlgEquiv.restrictNormalHom Kχ σ := by rw [map_pow, ← hsdef]; exact e'
    have h := hχπ _ _ e''
    rw [hχbpow, hχb, Multiplicative.ofAdd.apply_eq_iff_eq, eq_comm, ← Int.cast_natCast,
      ZMod.intCast_eq_intCast_iff_dvd_sub] at h

    rw [← dvd_neg, neg_sub] at h
    exact h

  have hρa : (Rep.ofAlgebraAutOnUnits K Kχ).ρ s (Additive.ofMul (Units.map (algebraMap K Kχ).toMonoidHom a))
      = Additive.ofMul (Units.map (algebraMap K Kχ).toMonoidHom a) :=
    (Additive.toMul (α := (Kχ)ˣ)).injective (Units.ext (s.commutes (a : K)))
  have hcoc : carryFun s hs hfin (A := Rep.ofAlgebraAutOnUnits K Kχ) (Additive.ofMul (Units.map (algebraMap K Kχ).toMonoidHom a))
      ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K Kχ) := carryFun_mem_cocycles2 s hs hfin _ hρa
  have hL2a := smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 p r hlevel χ hχlc hχ Kχ hKχ s hs hfin hsχ a α hα
  obtain ⟨FK, hFK, hUK⟩ := hlevel Kχ inferInstance

  have hord : orderOf s = Module.finrank K Kχ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  have hnormprod : ∀ w : Kχ, (∏ j ∈ Finset.range (orderOf s), (s ^ j) w) = algebraMap K Kχ (Algebra.norm K w) := by
    intro w
    rw [Algebra.norm_eq_prod_automorphisms, ← Fin.prod_univ_eq_prod_range]
    exact Fintype.prod_equiv ((finEquivZPowers hfin).trans (Equiv.subtypeUnivEquiv hs)) _ _ (fun j => rfl)

  have hiff : (H2π (Rep.ofAlgebraAutOnUnits K Kχ)).hom ⟨_, hcoc⟩ = 0 ↔ ∃ w : Kχ, Algebra.norm K w = (a : K) := by
    rw [carry_H2pi_eq_zero_iff s hs hfin _ hρa hcoc]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨((Additive.toMul (α := (Kχ)ˣ) b : (Kχ)ˣ) : Kχ), ?_⟩
      have e := congrArg (fun x => Additive.toMul (valHomL x)) hb
      simp only [map_sum, toMul_sum, toMul_valHomL_ρ] at e
      rw [toMul_valHomL, hnormprod] at e
      apply (algebraMap K Kχ).injective
      rw [e]
      rfl
    · rintro ⟨w, hw⟩
      have hw0 : w ≠ 0 := by
        rintro rfl
        rw [Algebra.norm_zero] at hw
        exact a.ne_zero hw.symm
      refine ⟨(Additive.ofMul (Units.mk0 w hw0) : Additive (Kχ)ˣ), ?_⟩
      have hinj : Function.Injective (fun x : Rep.ofAlgebraAutOnUnits K Kχ => Additive.toMul (valHomL x)) :=
        fun x y h => (Additive.toMul (α := (Kχ)ˣ)).injective (Units.ext h)
      apply hinj
      simp only [map_sum, toMul_sum, toMul_valHomL_ρ]
      show (∏ j ∈ Finset.range (orderOf s), (s ^ j) w) = _
      rw [hnormprod, hw]
      rfl

  have hsplit : ∀ (f g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω),
      (fun x => f x - g x) ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) →
      (f ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) ↔ g ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)) := by
    intro f g h
    have e : (fun x => f x - g x) = f - g := rfl
    rw [e] at h
    constructor
    · intro hf; have := sub_mem hf h; rwa [sub_sub_cancel] at this
    · intro hg; have := add_mem h hg; rwa [sub_add_cancel] at this
  have hkey : (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        ((MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
          ((χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
          : Rep.ofAlgebraAutOnUnits K Ω))
        ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω)
      ↔ ∃ w : Kχ, Algebra.norm K w = (a : K) := by
    refine (hsplit _ _ hL2a).trans ⟨fun h => ?_, fun h => ?_⟩
    · exact hiff.1 ((H2π_eq_zero_iff _).2 (mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 r hopen Kχ hcoc h))
    · exact unitsInflate2_mem_levelCoboundaries2 r Kχ ⟨FK, hFK, hUK⟩ ((H2π_eq_zero_iff _).1 (hiff.2 h))
  refine Iff.trans ?_ hkey

  constructor
  · intro hc
    exact cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r) (rG := r) (A := Kummer.kummerRep K Ω p)
      (B := Rep.ofAlgebraAutOnUnits K Ω) (MonoidHom.id _) (fun _ => rfl)
      (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap (fun _ _ => rfl) hc
  · intro hιc

    obtain ⟨Av, hAv⟩ : ∃ Av : Rep.ofAlgebraAutOnUnits K Ω, Additive.toMul (α := Ωˣ) Av = α := ⟨Additive.ofMul α, rfl⟩
    obtain ⟨Eα, hEα, hEαfix⟩ := exists_forall_mem_fixingSubgroup_ρ_eq (K := K) Av
    haveI := hEα
    obtain ⟨Fα, hFα, hUα⟩ := hlevel Eα inferInstance
    have hαfix : ∀ u : Ω ≃ₐ[K] Ω, r u ∈ Fα.fixingSubgroup → u • α = α := fun u hu => by
      have h := congrArg (Additive.toMul (α := Ωˣ)) (hEαfix u (hUα u hu))
      change u • Additive.toMul (α := Ωˣ) Av = Additive.toMul (α := Ωˣ) Av at h
      rwa [hAv] at h
    obtain ⟨Fχ, hFχ, hχ'⟩ := hχlc

    obtain ⟨Eμ, hEμdef⟩ : ∃ Eμ : IntermediateField K Ω,
        Eμ = IntermediateField.adjoin K (Set.range fun ζ : rootsOfUnity p Ω => ((ζ : Ωˣ) : Ω)) := ⟨_, rfl⟩
    haveI : FiniteDimensional K Eμ := by
      rw [hEμdef]
      exact IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    obtain ⟨Fμ, hFμ, hUμ⟩ := hlevel Eμ inferInstance
    have hμfix : ∀ (u : Ω ≃ₐ[K] Ω), r u ∈ Fμ.fixingSubgroup → ∀ x : Kummer.kummerRep K Ω p,
        (Kummer.kummerRep K Ω p).ρ u x = x := by
      intro u hu x
      have hu' := hUμ u hu
      rw [IntermediateField.mem_fixingSubgroup_iff] at hu'
      apply (Additive.toMul (α := rootsOfUnity p Ω)).injective
      apply Subtype.ext; apply Units.ext
      show u (((Additive.toMul (α := rootsOfUnity p Ω) x : rootsOfUnity p Ω) : Ωˣ) : Ω) = _
      apply hu'
      rw [hEμdef]
      exact IntermediateField.subset_adjoin K _ ⟨Additive.toMul (α := rootsOfUnity p Ω) x, rfl⟩
    haveI := hFα; haveI := hFχ; haveI := hFμ
    have hlc : IsLevelConstant₂ r (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2))) := by
      refine ⟨Fχ ⊔ Fα ⊔ Fμ, inferInstance, fun σ τ u u' hu hu' => ?_⟩
      have huχ : r u ∈ Fχ.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_left.trans le_sup_left) hu
      have huμ : r u ∈ Fμ.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hu
      have hu'α : r u' ∈ Fα.fixingSubgroup := IntermediateField.fixingSubgroup_antitone (le_sup_right.trans le_sup_left) hu'
      have hκ : Kummer.kummerCocycleRoots hα (τ * u') = Kummer.kummerCocycleRoots hα τ := by
        apply Subtype.ext
        show Kummer.kummerCocycle α (τ * u') = Kummer.kummerCocycle α τ
        rw [Kummer.kummerCocycle_apply, Kummer.kummerCocycle_apply, mul_smul, hαfix u' hu'α]
      dsimp only
      rw [hχ' σ u huχ, hκ, map_mul, Module.End.mul_apply, hμfix u huμ]

    have hp0 : ∀ x : Kummer.kummerRep K Ω p, (p : ℤ) • x = 0 := by
      intro x
      apply (Additive.toMul (α := rootsOfUnity p Ω)).injective
      apply Subtype.ext
      show (((Additive.toMul (α := rootsOfUnity p Ω) x) ^ (p : ℤ) : rootsOfUnity p Ω) : Ωˣ) = 1
      rw [zpow_natCast, SubmonoidClass.coe_pow]
      exact (mem_rootsOfUnity _ _).1 (Additive.toMul (α := rootsOfUnity p Ω) x).2
    have hρρ : ∀ (g h : Ω ≃ₐ[K] Ω) (x : Kummer.kummerRep K Ω p),
        (Kummer.kummerRep K Ω p).ρ g ((Kummer.kummerRep K Ω p).ρ h x) = (Kummer.kummerRep K Ω p).ρ (g * h) x :=
      fun g h x => by rw [map_mul]; rfl
    have hco : (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
          ∈ cocycles₂ (Kummer.kummerRep K Ω p) := by
      rw [mem_cocycles₂_iff]
      intro σ τ u
      dsimp only
      obtain ⟨δ, hδ⟩ := hχ σ τ
      have e1 : (Kummer.kummerRep K Ω p).ρ σ (Additive.ofMul (Kummer.kummerCocycleRoots hα (τ * u)))
          = (Kummer.kummerRep K Ω p).ρ σ ((Kummer.kummerRep K Ω p).ρ τ (Additive.ofMul (Kummer.kummerCocycleRoots hα u)))
            + (Kummer.kummerRep K Ω p).ρ σ (Additive.ofMul (Kummer.kummerCocycleRoots hα τ)) := by
        rw [← map_add]
        congr 1
        exact congrArg Additive.ofMul (Kummer.isMulCocycle₁_kummerCocycleRoots hα τ u)
      rw [e1, smul_add]
      simp only [map_smul, hρρ]
      exact key_cocycle _ _ (χ σ) (χ τ) (χ (σ * τ)) p δ hδ (hp0 _)

    have hinj := (continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero p r hlevel hopen).1
    have hc : (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
          ∈ levelCocycles₂ r (Kummer.kummerRep K Ω p) := ⟨hco, hlc⟩
    have h0 : continuousH2π r (Kummer.kummerRep K Ω p) ⟨_, hc⟩ = 0 := by
      apply hinj
      rw [map_zero]
      show continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω)
          (levelCocycles₂Map (rH := r) (rG := r) (A := Kummer.kummerRep K Ω p) (B := Rep.ofAlgebraAutOnUnits K Ω)
            (MonoidHom.id _) (fun _ => rfl) (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
            (fun _ _ => rfl) ⟨_, hc⟩) = 0
      rw [continuousH2π_eq_zero_iff]
      exact hιc
    exact (continuousH2π_eq_zero_iff r _ ⟨_, hc⟩).1 h0

end S_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
end P2MW
export P2MW.S_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq (solution)
