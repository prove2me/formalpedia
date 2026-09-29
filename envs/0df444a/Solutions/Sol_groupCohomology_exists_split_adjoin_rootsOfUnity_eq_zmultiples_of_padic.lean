-- Prove2me | solution 1 for groupCohomology.exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/954f337e-bc3d-5c0d-ac7b-d4f6120f1978

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCocycles2
import Theorems.Thm_groupCohomology_mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits
import Theorems.Thm_groupCohomology_exists_unitsInflate2_eq_of_le
import Theorems.Thm_ExtCitation_LocalLevel_natCard_H2_units_eq_natCard_of_isCyclic
import Theorems.Thm_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_adjoin_rootsOfUnity_padic_mono
import Theorems.Thm_IntermediateField_norm_algebraNorm_eq_pow_finrank_padic
import Theorems.Thm_IntermediateField_exists_uniformiser_padic
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic.groupCohomology IntermediateField"

namespace groupCohomology
p2m_export "groupCohomology" "H2 H2π congr cocycles₂ cocycles π H2_induction_on H2π_eq_zero_iff levelCocycles₂ continuousH2 continuousH2π continuousH2π_eq_zero_iff unitsInflate₂ carryFun unitsInflate2_mem_levelCocycles2 mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits exists_unitsInflate2_eq_of_le carryFun_mem_cocycles2 carry_H2pi_eq_zero_iff"
p2m_open "groupCohomology"

private noncomputable def valHom {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] :
    (Rep.ofAlgebraAutOnUnits K L) →+ Additive L where
  toFun x := Additive.ofMul (((Additive.toMul (α := Lˣ) x) : Lˣ) : L)
  map_zero' := rfl
  map_add' x y := congrArg Additive.ofMul (Units.val_mul (Additive.toMul (α := Lˣ) x) (Additive.toMul (α := Lˣ) y))

private lemma toMul_valHom {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (x : Rep.ofAlgebraAutOnUnits K L) :
    Additive.toMul (valHom x) = ((Additive.toMul (α := Lˣ) x : Lˣ) : L) := rfl

private lemma toMul_valHom_ρ {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Rep.ofAlgebraAutOnUnits K L) :
    Additive.toMul (valHom ((Rep.ofAlgebraAutOnUnits K L).ρ σ x)) = σ ((Additive.toMul (α := Lˣ) x : Lˣ) : L) := rfl

set_option maxHeartbeats 6400000 in

private theorem exists_generator_H2_units_of_cyclic_unramified (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] [Normal K L]
    (φ : L ≃ₐ[K] L) (hφ : ∀ σ, σ ∈ Subgroup.zpowers φ)
    (hunram : ∀ x : L, x ≠ 0 → ∃ y : K, ‖(x : PadicAlgCl q)‖ = ‖((y : PadicAlgCl q))‖) :
    ∃ c₀ : H2 (Rep.ofAlgebraAutOnUnits K L), addOrderOf c₀ = Module.finrank K L ∧ AddSubgroup.zmultiples c₀ = ⊤ := by
  haveI : IsGalois K L := IsGalois.mk
  obtain ⟨π, hπ0, hπ1, hπv⟩ := IntermediateField.exists_uniformiser_padic q K
  have hfin : IsOfFinOrder φ := isOfFinOrder_of_finite φ
  have hord : orderOf φ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hφ, IsGalois.card_aut_eq_finrank]
  have hmpos : 0 < Module.finrank K L := Module.finrank_pos

  have hπK : (π : K) ≠ 0 := fun h => (norm_pos_iff.1 hπ0) (by rw [h]; rfl)
  have hπL : algebraMap K L π ≠ 0 := (map_ne_zero _).2 hπK
  obtain ⟨πL, hπLval⟩ : ∃ πL : (L)ˣ, (πL : L) = algebraMap K L π := ⟨Units.mk0 _ hπL, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : Rep.ofAlgebraAutOnUnits K L, Additive.toMul (α := (L)ˣ) a = πL := ⟨Additive.ofMul πL, rfl⟩
  have hρa1 : ∀ σ : L ≃ₐ[K] L, (Rep.ofAlgebraAutOnUnits K L).ρ σ a = a := fun σ =>
    (Additive.toMul (α := (L)ˣ)).injective (Units.ext (by
      show σ ((Additive.toMul (α := (L)ˣ) a : (L)ˣ) : L) = ((Additive.toMul (α := (L)ˣ) a : (L)ˣ) : L)
      rw [hadef, hπLval]
      exact σ.commutes π))
  have hρa : ∀ (σ : L ≃ₐ[K] L) (i : ℤ), (Rep.ofAlgebraAutOnUnits K L).ρ σ (i • a) = i • a := by
    intro σ i
    rw [map_zsmul, hρa1]

  have hz : ∀ i : ℤ, carryFun φ hφ hfin (i • a) ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L) :=
    fun i => carryFun_mem_cocycles2 φ hφ hfin (i • a) (hρa φ i)
  have hcarry_smul : ∀ i : ℤ, carryFun φ hφ hfin (i • a) = i • carryFun φ hφ hfin a := by
    intro i; funext p
    simp only [carryFun, Pi.smul_apply]
    split_ifs
    · rfl
    · rw [smul_zero]
  have hz1 : carryFun φ hφ hfin a ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L) := by
    have h := hz 1; rwa [one_zsmul] at h
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : H2 (Rep.ofAlgebraAutOnUnits K L),
      c₀ = (H2π _).hom ⟨carryFun φ hφ hfin a, hz1⟩ := ⟨_, rfl⟩
  have hsmul_c₀ : ∀ i : ℤ, i • c₀ = (H2π _).hom ⟨carryFun φ hφ hfin (i • a), hz i⟩ := by
    intro i
    rw [hc₀, ← map_zsmul]
    congr 1
    apply Subtype.ext
    show i • carryFun φ hφ hfin a = carryFun φ hφ hfin (i • a)
    exact (hcarry_smul i).symm

  have hnormprod : ∀ w : L, (∏ j ∈ Finset.range (orderOf φ), (φ ^ j) w) = algebraMap K L (Algebra.norm K w) := by
    intro w
    rw [Algebra.norm_eq_prod_automorphisms, ← Fin.prod_univ_eq_prod_range]
    exact Fintype.prod_equiv ((finEquivZPowers hfin).trans (Equiv.subtypeUnivEquiv hφ)) _ _ (fun j => rfl)

  have hcrit : ∀ i : ℤ, i • c₀ = 0 ↔ (Module.finrank K L : ℤ) ∣ i := by
    intro i
    rw [hsmul_c₀, carry_H2pi_eq_zero_iff φ hφ hfin (i • a) (hρa φ i) (hz i)]
    constructor
    · rintro ⟨b, hb⟩

      obtain ⟨w, hw⟩ : ∃ w : L, w = ((Additive.toMul (α := (L)ˣ) b : (L)ˣ) : L) := ⟨_, rfl⟩
      have hw0 : w ≠ 0 := by rw [hw]; exact Units.ne_zero _
      have hbL : algebraMap K L (Algebra.norm K w) = (algebraMap K L π) ^ i := by
        have e := congrArg (fun x => Additive.toMul (valHom x)) hb
        simp only [map_sum, map_zsmul, toMul_sum, toMul_zsmul, toMul_valHom_ρ] at e
        rw [toMul_valHom, hadef, hπLval] at e
        simp only [← hw] at e
        rw [hnormprod] at e
        exact e

      have h1 : ‖(w : PadicAlgCl q)‖ ^ Module.finrank K L = ‖(π : PadicAlgCl q)‖ ^ i := by
        rw [← IntermediateField.norm_algebraNorm_eq_pow_finrank_padic q K L w]
        have e := congrArg (algebraMap L (PadicAlgCl q)) hbL
        rw [map_zpow₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e
        have e' := congrArg (fun z : PadicAlgCl q => ‖z‖) e
        rw [norm_zpow] at e'
        exact e'
      obtain ⟨y, hy⟩ := hunram w hw0
      rw [hy] at h1
      have hy0 : y ≠ 0 := by
        rintro rfl
        apply zpow_ne_zero i (norm_pos_iff.1 hπ0 |> norm_ne_zero_iff.2)
        rw [← h1]
        simp [hmpos.ne']
      obtain ⟨j, hj⟩ := hπv y hy0
      rw [hj, ← zpow_natCast, ← zpow_mul] at h1
      have hij : j * (Module.finrank K L : ℤ) = i := zpow_right_injective₀ hπ0 (ne_of_lt hπ1) h1
      exact ⟨j, by rw [← hij, mul_comm]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k • a, ?_⟩
      simp only [hρa, Finset.sum_const, Finset.card_range, hord, hk]
      rw [← natCast_zsmul, smul_smul]

  have hordc : addOrderOf c₀ = Module.finrank K L := by
    apply Nat.dvd_antisymm
    · apply addOrderOf_dvd_of_nsmul_eq_zero
      rw [← natCast_zsmul]
      exact (hcrit _).2 (dvd_refl _)
    · have h := (hcrit (addOrderOf c₀)).1 (by rw [natCast_zsmul]; exact addOrderOf_nsmul_eq_zero c₀)
      exact Int.natCast_dvd_natCast.1 h

  have hcard : Nat.card (H2 (Rep.ofAlgebraAutOnUnits K L)) = Module.finrank K L := by
    haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨φ, hφ⟩⟩
    haveI : FiniteDimensional ℚ_[q] (L.restrictScalars ℚ_[q]) := FiniteDimensional.trans ℚ_[q] K L
    letI : MulSemiringAction (L ≃ₐ[K] L) (L.restrictScalars ℚ_[q]) :=
      (inferInstance : MulSemiringAction (L ≃ₐ[K] L) L)
    haveI : FaithfulSMul (L ≃ₐ[K] L) (L.restrictScalars ℚ_[q]) :=
      (inferInstance : FaithfulSMul (L ≃ₐ[K] L) L)
    letI : MulDistribMulAction (L ≃ₐ[K] L) ((L.restrictScalars ℚ_[q]))ˣ :=
      (inferInstance : MulDistribMulAction (L ≃ₐ[K] L) (L)ˣ)
    have h := ExtCitation.LocalLevel.natCard_H2_units_eq_natCard_of_isCyclic q (L.restrictScalars ℚ_[q]) (L ≃ₐ[K] L)
      (fun g x => by
        show g (algebraMap ℚ_[q] L x) = algebraMap ℚ_[q] L x
        rw [IsScalarTower.algebraMap_apply ℚ_[q] K L]; exact g.commutes _)
      (fun g u => rfl)
    rw [IsGalois.card_aut_eq_finrank] at h
    exact h
  refine ⟨c₀, hordc, ?_⟩
  haveI : Finite (H2 (Rep.ofAlgebraAutOnUnits K L)) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hmpos.ne')
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples, hordc, hcard]

set_option maxHeartbeats 6400000 in

private theorem exists_split_eq_zmultiples_of_generator (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] [Normal K L]
    (c₀ : H2 (Rep.ofAlgebraAutOnUnits K L)) (htop : AddSubgroup.zmultiples c₀ = ⊤) :
    ∃ u : continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)), addOrderOf u = addOrderOf c₀ ∧
      {x | ∃ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
          (h : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) ⟨unitsInflate₂ L f, h⟩}
        = (AddSubgroup.zmultiples u : Set _) := by
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsGalois.mk
  haveI : IsGalois K (PadicAlgCl q) := IsGalois.tower_top_intermediateField K
  obtain ⟨FL, hFL, hUL⟩ := hlevel L inferInstance
  obtain ⟨inf, hinf⟩ := exists_linearMap_H2_continuousH2_ofAlgebraAutOnUnits r L ⟨FL, hFL, hUL⟩
  have hlc : ∀ f : cocycles₂ (Rep.ofAlgebraAutOnUnits K L),
      unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) :=
    fun f => unitsInflate2_mem_levelCocycles2 r L ⟨FL, hFL, hUL⟩ f.2
  have hinj : Function.Injective inf := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using H2_induction_on with
    | h f =>
      rw [hinf f (hlc f), continuousH2π_eq_zero_iff] at hy
      exact (H2π_eq_zero_iff f).2
        (mem_coboundaries2_of_unitsInflate2_mem_levelCoboundaries2 r hopen L f.2 hy)
  refine ⟨inf c₀, addOrderOf_injective inf.toAddMonoidHom hinj c₀, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨f, hf, h, rfl⟩
    have hmem : (H2π (Rep.ofAlgebraAutOnUnits K L)).hom ⟨f, hf⟩ ∈ AddSubgroup.zmultiples c₀ := by
      rw [htop]; exact AddSubgroup.mem_top _
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
    refine ⟨k, ?_⟩
    rw [← map_zsmul, hk, hinf ⟨f, hf⟩ h]
    rfl
  · rintro ⟨k, rfl⟩
    rw [← map_zsmul]
    induction (k • c₀) using H2_induction_on with
    | h f => exact ⟨f, f.2, hlc f, hinf f (hlc f)⟩

end groupCohomology

set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] :
    (∃ u : continuousH2 r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)),
      addOrderOf u = Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∧
      {x | ∃ (f : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) × ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) → Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
          (h : unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) ⟨unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f, h⟩}
        = (AddSubgroup.zmultiples u : Set _)) ∧
    (∀ (N' : ℕ), N ∣ N' →
      ∀ [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1})]
        [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1})],
      {x | ∃ (f : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) × ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) → Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
          (h : unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) ⟨unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) f, h⟩}
        ⊆ {x | ∃ (f : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1})) × ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1})) → Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1}))ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1})))
          (h : unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1}) f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) ⟨unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1}) f, h⟩}) := by
  refine ⟨?_, fun N' hNN' _ _ => ?_⟩
  ·
    obtain ⟨φ, hφ, -⟩ := IntermediateField.exists_generator_frobenius_adjoin_rootsOfUnity_padic q K N hN
    obtain ⟨c₀, hordc, htop⟩ := groupCohomology.exists_generator_H2_units_of_cyclic_unramified q K
      (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) φ hφ
      (fun x hx => IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic q K N hN x hx)
    obtain ⟨u, hu, hsplit⟩ := groupCohomology.exists_split_eq_zmultiples_of_generator q K r hlevel hopen
      (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) c₀ htop
    exact ⟨u, hu.trans hordc, hsplit⟩
  ·
    rintro x ⟨f, hf, h, rfl⟩
    obtain ⟨f', hf', heq⟩ := groupCohomology.exists_unitsInflate2_eq_of_le
      (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) _
      (IntermediateField.adjoin_rootsOfUnity_padic_mono q K hNN') f hf
    refine ⟨f', hf', (by rw [heq]; exact h), ?_⟩
    congr 1
    exact Subtype.ext heq.symm

end S_groupCohomology_exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic
end P2MW
export P2MW.S_groupCohomology_exists_split_adjoin_rootsOfUnity_eq_zmultiples_of_padic (solution)
