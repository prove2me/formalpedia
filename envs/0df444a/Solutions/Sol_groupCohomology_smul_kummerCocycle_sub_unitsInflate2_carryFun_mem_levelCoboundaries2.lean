-- Prove2me | solution 1 for groupCohomology.smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/257b2af0-61d5-54a4-9138-429c524453f4

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ congr cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff IsLevelConstant₁ levelCoboundaries₂ mem_levelCoboundaries₂_iff Kummer.kummerCocycle_apply Kummer.kummerRep Kummer.kummerCocycleRoots Kummer.coe_kummerCocycleRoots unitsInflate₁ unitsInflate₂ cyclicLog carryFun"
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
p2m_export "groupCohomology" "d₁₂ congr cocycles₂ d₁₂_hom_apply d₁₂_apply_mem_cocycles₂ map mem_cocycles₂_iff IsLevelConstant₁ levelCoboundaries₂ mem_levelCoboundaries₂_iff Kummer.kummerCocycle_apply Kummer.kummerRep Kummer.kummerCocycleRoots Kummer.coe_kummerCocycleRoots unitsInflate₁ unitsInflate₂ cyclicLog carryFun"
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

private theorem key_nocarry {V : Type*} [AddCommGroup V] (X Y : V) (Lσ Lτ p mσ mτ mστ : ℤ) :
    mτ • p • X - (Lτ + p * mτ) • X - (mστ • p • X - (Lσ + Lτ + p * mστ) • X) + (mσ • p • X - (Lσ + p * mσ) • Y)
      = (Lσ + p * mσ) • X - (Lσ + p * mσ) • Y - 0 := by
  module

private theorem key_carry {V : Type*} [AddCommGroup V] (X Y : V) (Lσ Lτ p mσ mτ mστ : ℤ) :
    mτ • p • X - (Lτ + p * mτ) • X - (mστ • p • X - (Lσ + Lτ - p + p * mστ) • X) + (mσ • p • X - (Lσ + p * mσ) • Y)
      = (Lσ + p * mσ) • X - (Lσ + p * mσ) • Y - p • X := by
  module

theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ℤ) (hχlc : IsLevelConstant₁ r χ)
    (hχ : ∀ σ τ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (Kχ : IntermediateField K Ω) [FiniteDimensional K Kχ] [Normal K Kχ]
    (hKχ : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ Kχ.fixingSubgroup ↔ (p : ℤ) ∣ χ σ)
    (s : Kχ ≃ₐ[K] Kχ) (hs : ∀ g, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (hsχ : ∀ σ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ - (cyclicLog s hs hfin (AlgEquiv.restrictNormalHom Kχ σ) : ℤ))
    (a : Kˣ) (α : Ωˣ) (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
          ((χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
        - unitsInflate₂ Kχ
            (carryFun s hs hfin (A := Rep.ofAlgebraAutOnUnits K Kχ)
              (Additive.ofMul (Units.map (algebraMap K Kχ).toMonoidHom a))) g)
      ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by
  classical

  obtain ⟨Av, hAv⟩ : ∃ Av : Rep.ofAlgebraAutOnUnits K Ω, Additive.toMul (α := Ωˣ) Av = α := ⟨Additive.ofMul α, rfl⟩
  obtain ⟨av, hav⟩ : ∃ av : Rep.ofAlgebraAutOnUnits K Ω,
      Additive.toMul (α := Ωˣ) av = Units.map (algebraMap K Ω).toMonoidHom a := ⟨Additive.ofMul _, rfl⟩
  have hga : ∀ g : Ω ≃ₐ[K] Ω, (Rep.ofAlgebraAutOnUnits K Ω).ρ g av = av := by
    intro g; apply ext_Ω
    rw [coe_ρΩ, hav, Units.coe_map]
    exact g.commutes _
  have hpA : ∀ g : Ω ≃ₐ[K] Ω, (p : ℤ) • (Rep.ofAlgebraAutOnUnits K Ω).ρ g Av = av := by
    intro g
    rw [← map_zsmul]
    rw [← hga g]
    congr 1
    apply ext_Ω
    show (((Additive.toMul (α := Ωˣ) Av) ^ (p : ℤ) : Ωˣ) : Ω) = _
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast, hAv, hav, Units.coe_map, ← hα]
    rfl

  have hιc : ∀ σ τ : Ω ≃ₐ[K] Ω,
      ((MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
          ((χ σ) • (Kummer.kummerRep K Ω p).ρ σ (Additive.ofMul (Kummer.kummerCocycleRoots hα τ)))
        : Rep.ofAlgebraAutOnUnits K Ω)
        = (χ σ) • ((Rep.ofAlgebraAutOnUnits K Ω).ρ (σ * τ) Av - (Rep.ofAlgebraAutOnUnits K Ω).ρ σ Av) := by
    intro σ τ
    (first | rw [map_smul] | rw [map_zsmul] | erw [map_zsmul])
    congr 1
    apply ext_Ω
    show ((σ • (Kummer.kummerCocycleRoots hα τ : Ωˣ) : Ωˣ) : Ω)
      = ((Additive.toMul (α := Ωˣ) ((Rep.ofAlgebraAutOnUnits K Ω).ρ (σ * τ) Av)
          / Additive.toMul (α := Ωˣ) ((Rep.ofAlgebraAutOnUnits K Ω).ρ σ Av) : Ωˣ) : Ω)
    rw [Units.val_div_eq_div_val, coe_ρΩ, coe_ρΩ, hAv, Kummer.coe_kummerCocycleRoots, Kummer.kummerCocycle_apply]
    show σ (((τ • α / α : Ωˣ)) : Ω) = _
    rw [Units.val_div_eq_div_val, map_div₀, AlgEquiv.mul_apply]
    rfl

  obtain ⟨L, hL⟩ : ∃ L : (Ω ≃ₐ[K] Ω) → ℕ, ∀ σ, L σ = cyclicLog s hs hfin (AlgEquiv.restrictNormalHom Kχ σ) :=
    ⟨_, fun _ => rfl⟩
  have hcarry : ∀ σ τ : Ω ≃ₐ[K] Ω,
      unitsInflate₂ Kχ (carryFun s hs hfin (A := Rep.ofAlgebraAutOnUnits K Kχ)
          (Additive.ofMul (Units.map (algebraMap K Kχ).toMonoidHom a))) (σ, τ)
        = if orderOf s ≤ L σ + L τ then av else 0 := by
    intro σ τ
    rw [unitsInflate₂_eq, hL, hL]
    simp only [carryFun]
    split_ifs with h
    · apply ext_Ω
      rw [coe_ιA, hav]
      rfl
    · exact map_zero _

  have hLpow : ∀ σ, s ^ (L σ) = AlgEquiv.restrictNormalHom Kχ σ := by
    intro σ
    have e := (finEquivZPowers hfin).apply_symm_apply ⟨AlgEquiv.restrictNormalHom Kχ σ, hs _⟩
    rw [finEquivZPowers_apply] at e
    have e' := congrArg Subtype.val e
    rw [hL]
    exact e'
  have hLlt : ∀ σ, L σ < orderOf s := fun σ => by rw [hL]; exact Fin.is_lt _
  have hLmul : ∀ σ τ, L (σ * τ) + orderOf s * (if orderOf s ≤ L σ + L τ then 1 else 0) = L σ + L τ := by
    intro σ τ
    have hmod : L (σ * τ) ≡ L σ + L τ [MOD orderOf s] := by
      rw [← pow_eq_pow_iff_modEq, pow_add, hLpow, hLpow, hLpow, map_mul]
    have h1 := hLlt σ; have h2 := hLlt τ; have h3 := hLlt (σ * τ)
    split_ifs with h
    ·
      have : (L σ + L τ) % orderOf s = L σ + L τ - orderOf s := by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      rw [Nat.ModEq, Nat.mod_eq_of_lt h3, this] at hmod
      omega
    · rw [Nat.ModEq, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (by omega)] at hmod
      omega

  have hordp : orderOf s = 1 ∨ orderOf s = p := by
    haveI : IsGalois K Kχ := IsGalois.mk
    let χb : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod p) :=
      { toFun := fun σ => Multiplicative.ofAdd ((χ σ : ℤ) : ZMod p)
        map_one' := by
          have h := hχ 1 1
          rw [mul_one] at h
          have h0 : ((χ 1 : ℤ) : ZMod p) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simpa using h
          show Multiplicative.ofAdd ((χ 1 : ℤ) : ZMod p) = 1
          rw [h0]; rfl
        map_mul' := fun σ τ => by
          show Multiplicative.ofAdd ((χ (σ * τ) : ℤ) : ZMod p)
            = Multiplicative.ofAdd ((χ σ : ℤ) : ZMod p) * Multiplicative.ofAdd ((χ τ : ℤ) : ZMod p)
          rw [← ofAdd_add, ← Int.cast_add]
          congr 1
          rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
          simpa using hχ σ τ }
    have hker : χb.ker = Kχ.fixingSubgroup := by
      ext σ
      rw [MonoidHom.mem_ker, hKχ]
      show Multiplicative.ofAdd ((χ σ : ℤ) : ZMod p) = 1 ↔ _
      rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcard : orderOf s = Kχ.fixingSubgroup.index := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank,
        IntermediateField.finrank_eq_fixingSubgroup_index]
    have hdvd : Kχ.fixingSubgroup.index ∣ p := by
      rw [← hker, Subgroup.index_ker]
      have := Subgroup.card_subgroup_dvd_card χb.range
      rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod p)), Fintype.card_multiplicative, ZMod.card] at this
    rw [hcard]
    exact (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd

  choose m hm using fun σ => hsχ σ
  simp only [← hL] at hm
  haveI : Algebra.IsAlgebraic K Ω := inferInstance
  have eχ : ∀ x, χ x = (L x : ℤ) + (p : ℤ) * m x := fun x => by linarith [hm x]

  obtain ⟨Eα, hEα, hEαfix⟩ := exists_forall_mem_fixingSubgroup_ρ_eq (K := K) Av
  haveI := hEα
  obtain ⟨Fα, hFα, hUα⟩ := hlevel Eα inferInstance
  obtain ⟨Fχ, hFχ, hχ'⟩ := hχlc
  obtain ⟨FK, hFK, hUK⟩ := hlevel Kχ inferInstance
  haveI := hFα; haveI := hFχ; haveI := hFK
  have hLlc : ∀ σ u, r u ∈ FK.fixingSubgroup → L (σ * u) = L σ := by
    intro σ u hu; rw [hL, hL, map_mul, (restrictNormalHom_eq_one_iff Kχ u).2 (hUK u hu), mul_one]
  have hmlc : ∀ σ u, r u ∈ (Fχ ⊔ FK).fixingSubgroup → m (σ * u) = m σ := by
    intro σ u hu
    have h1 := hm (σ * u)
    rw [hχ' σ u (IntermediateField.fixingSubgroup_antitone le_sup_left hu),
      hLlc σ u (IntermediateField.fixingSubgroup_antitone le_sup_right hu)] at h1
    exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (h1.symm.trans (hm σ))

  refine (mem_levelCoboundaries₂_iff r _ _).2
    ⟨fun σ => m σ • av - χ σ • (Rep.ofAlgebraAutOnUnits K Ω).ρ σ Av, ⟨Fχ ⊔ FK ⊔ Fα, inferInstance, fun σ u hu => ?_⟩, ?_⟩
  · have hu1 : r u ∈ (Fχ ⊔ FK).fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hu
    have hu2 : r u ∈ Fα.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hu
    simp only
    rw [hmlc σ u hu1, hχ' σ u (IntermediateField.fixingSubgroup_antitone le_sup_left hu1), map_mul,
      Module.End.mul_apply, hEαfix u (hUα u hu2)]
  · funext ⟨σ, τ⟩
    rw [d₁₂_hom_apply]
    dsimp only
    rw [hιc σ τ, hcarry σ τ]
    have hρρ : ∀ (g h : Ω ≃ₐ[K] Ω) (x : Rep.ofAlgebraAutOnUnits K Ω),
        (Rep.ofAlgebraAutOnUnits K Ω).ρ g ((Rep.ofAlgebraAutOnUnits K Ω).ρ h x) = (Rep.ofAlgebraAutOnUnits K Ω).ρ (g * h) x :=
      fun g h x => by rw [map_mul]; rfl
    simp only [map_sub, map_smul, smul_sub, hga, hρρ]
    rw [eχ σ, eχ τ, eχ (σ * τ)]
    split_ifs with hc
    · have hp' : orderOf s = p := hordp.resolve_left (fun h1 => by have := hLlt σ; have := hLlt τ; omega)
      have e := hLmul σ τ
      rw [if_pos hc, hp', mul_one] at e
      have eL : (L (σ * τ) : ℤ) = L σ + L τ - p := by
        have e' := congrArg (Nat.cast : ℕ → ℤ) e
        push_cast at e'
        linarith
      rw [eL, ← hpA (σ * τ)]
      exact key_carry _ _ _ _ _ _ _ _
    · have e := hLmul σ τ
      rw [if_neg hc, mul_zero, add_zero] at e
      have eL : (L (σ * τ) : ℤ) = L σ + L τ := by exact_mod_cast e
      rw [eL, ← hpA (σ * τ)]
      exact key_nocarry _ _ _ _ _ _ _ _

end S_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
end P2MW
export P2MW.S_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2 (solution)
