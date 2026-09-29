-- Prove2me | solution 1 for exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f42e7a99-f2eb-53a0-8883-1a41ea866df9

import Mathlib
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace OrderCharLift

theorem isIntegral_int_map {A B : Type*} [CommRing A] [CommRing B] {ia : Algebra ℤ A}
    {ib : Algebra ℤ B} (f : A →+* B) {a : A} (h : @IsIntegral ℤ A _ _ ia a) :
    @IsIntegral ℤ B _ _ ib (f a) := by
  obtain ⟨q, hq, hqa⟩ := h
  refine ⟨q, hq, ?_⟩
  have h' := congrArg f hqa
  rw [Polynomial.hom_eval₂, map_zero] at h'
  convert h' using 2 <;> first | rfl | exact Subsingleton.elim _ _

theorem isIntegral_rat_of_int {B : Type*} [CommRing B] {ib : Algebra ℤ B} [Algebra ℚ B] {b : B}
    (h : @IsIntegral ℤ B _ _ ib b) : IsIntegral ℚ b := by
  obtain ⟨q, hq, hqb⟩ := h
  refine ⟨q.map (Int.castRingHom ℚ), hq.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  convert hqb using 2 <;> first | rfl | exact Subsingleton.elim _ _

section Order

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R]

theorem finiteDimensional_fractionRing : FiniteDimensional ℚ (FractionRing R) := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite ℤ R)
  let T : Finset (FractionRing R) := s.image (algebraMap R (FractionRing R))
  have hTint : ∀ x ∈ T, IsIntegral ℚ x := by
    intro x hx
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hx
    have h : IsIntegral ℤ (algebraMap R (FractionRing R) r) :=
      isIntegral_int_map (algebraMap R (FractionRing R)) (Algebra.IsIntegral.isIntegral r)
    exact isIntegral_rat_of_int h
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (T : Set (FractionRing R))) :=
    IntermediateField.finiteDimensional_adjoin hTint
  have hR : ∀ r : R, algebraMap R (FractionRing R) r ∈
      IntermediateField.adjoin ℚ (T : Set (FractionRing R)) := by
    intro r
    have hr : r ∈ Submodule.span ℤ (s : Set R) := by rw [hs]; exact Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin ℚ _
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n
  have htop : IntermediateField.adjoin ℚ (T : Set (FractionRing R)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    exact div_mem (hR a) (hR b)
  haveI : FiniteDimensional ℚ (⊤ : IntermediateField ℚ (FractionRing R)) := by
    rw [← htop]; infer_instance
  exact Module.Finite.equiv
    (IntermediateField.topEquiv (F := ℚ) (E := FractionRing R)).toLinearEquiv

theorem numberField_fractionRing : NumberField (FractionRing R) :=
  { to_charZero := inferInstance
    to_finiteDimensional := finiteDimensional_fractionRing R }

def toRingOfIntegers : R →+* 𝓞 (FractionRing R) where
  toFun r := ⟨algebraMap R (FractionRing R) r,
    isIntegral_int_map (algebraMap R (FractionRing R)) (Algebra.IsIntegral.isIntegral r)⟩
  map_one' := RingOfIntegers.eq_iff.mp (by simp only [RingOfIntegers.map_mk, map_one])
  map_mul' _ _ := RingOfIntegers.eq_iff.mp (by simp only [RingOfIntegers.map_mk, map_mul])
  map_zero' := RingOfIntegers.eq_iff.mp (by simp only [RingOfIntegers.map_mk, map_zero])
  map_add' _ _ := RingOfIntegers.eq_iff.mp (by simp only [RingOfIntegers.map_mk, map_add])

omit [CharZero R] in
theorem coe_toRingOfIntegers (r : R) :
    ((toRingOfIntegers R r : 𝓞 (FractionRing R)) : FractionRing R) =
      algebraMap R (FractionRing R) r := rfl

omit [CharZero R] in
theorem toRingOfIntegers_injective : Function.Injective (toRingOfIntegers R) := by
  intro x y h
  have h' := congrArg (fun z : 𝓞 (FractionRing R) => (z : FractionRing R)) h
  simp only [coe_toRingOfIntegers] at h'
  exact IsFractionRing.injective R (FractionRing R) h'

end Order

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff
    {S : Type*} [CommRing S] [IsDedekindDomain S] (K : Type*) [Field K] [Algebra S K]
    [IsFractionRing S K] (v : HeightOneSpectrum S) (r : S) :
    algebraMap S (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  change ¬ Valued.v ((algebraMap S K r : K) : v.adicCompletion K) = 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact ⟨fun h => lt_of_le_of_ne (HeightOneSpectrum.valuation_le_one v r) h, fun h => h.ne⟩

section Main

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R]

theorem main (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p] (π : R →+* F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
        (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
        (ψ : R →+* O) (F' : Type) (_ : Field F') (_ : Algebra F F')
        (ι : IsLocalRing.ResidueField O →+* F'),
      Function.Injective ψ ∧
      Ideal.comap ψ (IsLocalRing.maximalIdeal O) = RingHom.ker π ∧
      (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      ∀ x, ι (IsLocalRing.residue O (ψ x)) = algebraMap F F' (π x) := by
  classical
  haveI : NumberField (FractionRing R) := numberField_fractionRing R

  haveI hPprime : (RingHom.ker π).IsPrime := RingHom.ker_isPrime π
  have hpP : (p : R) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero F p

  letI : Algebra R (𝓞 (FractionRing R)) := (toRingOfIntegers R).toAlgebra
  have halg : ∀ x, algebraMap R (𝓞 (FractionRing R)) x = toRingOfIntegers R x := fun _ => rfl
  haveI : IsScalarTower ℤ R (𝓞 (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.IsIntegral R (𝓞 (FractionRing R)) :=
    ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩

  have hbot : Ideal.comap (algebraMap R (𝓞 (FractionRing R))) ⊥ ≤ RingHom.ker π := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot, halg] at hx
    have hx0 : x = 0 := toRingOfIntegers_injective R (by rw [hx, map_zero])
    rw [hx0]; exact zero_mem _
  obtain ⟨Q, -, hQprime, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker π) (⊥ : Ideal (𝓞 (FractionRing R))) hbot
  have hpQ : (p : 𝓞 (FractionRing R)) ∈ Q := by
    have : algebraMap R (𝓞 (FractionRing R)) (p : R) ∈ Q := by
      rw [← Ideal.mem_comap, hQP]; exact hpP
    rwa [map_natCast] at this
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpQ)
  let v : HeightOneSpectrum (𝓞 (FractionRing R)) := ⟨Q, hQprime, hQne⟩
  haveI : Finite (𝓞 (FractionRing R) ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQne

  let O : Type := v.adicCompletionIntegers (FractionRing R)
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) O :=
    HeightOneSpectrum.isAdicComplete_adicCompletionIntegers (FractionRing R) v
  haveI : Finite (𝓞 (FractionRing R) ⧸ v.asIdeal) := ‹Finite (𝓞 (FractionRing R) ⧸ Q)›
  haveI : Finite (IsLocalRing.ResidueField O) :=
    HeightOneSpectrum.finite_residueField_adicCompletionIntegers (FractionRing R) v
  haveI : CharZero (v.adicCompletion (FractionRing R)) :=
    charZero_of_injective_algebraMap
      (algebraMap (FractionRing R) (v.adicCompletion (FractionRing R))).injective
  haveI : CharZero O := inferInstance
  let ψ : R →+* O := (algebraMap (𝓞 (FractionRing R)) O).comp (toRingOfIntegers R)
  have hmem : ∀ x : R, ψ x ∈ IsLocalRing.maximalIdeal O ↔ x ∈ RingHom.ker π := by
    intro x
    show algebraMap (𝓞 (FractionRing R)) O (toRingOfIntegers R x) ∈ _ ↔ _
    rw [algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (FractionRing R) v, ← hQP,
      Ideal.mem_comap]
    rfl
  have hψinj : Function.Injective ψ :=
    (FaithfulSMul.algebraMap_injective (𝓞 (FractionRing R)) O).comp (toRingOfIntegers_injective R)
  have hcomap : Ideal.comap ψ (IsLocalRing.maximalIdeal O) = RingHom.ker π := by
    ext x; rw [Ideal.mem_comap]; exact hmem x

  let κ : Type := IsLocalRing.ResidueField O
  let F' : Type := AlgebraicClosure F
  let r : R →+* κ := (IsLocalRing.residue O).comp ψ
  letI : Algebra R κ := r.toAlgebra
  haveI : Algebra.IsIntegral R κ := Algebra.IsIntegral.of_finite R κ
  let χ : R →+* F' := (algebraMap F F').comp π
  have hQ : (⊥ : Ideal κ).comap (algebraMap R κ) = RingHom.ker χ := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]
    show IsLocalRing.residue O (ψ x) = 0 ↔ algebraMap F F' (π x) = 0
    rw [IsLocalRing.residue_eq_zero_iff, hmem, map_eq_zero_iff _ (algebraMap F F').injective,
      RingHom.mem_ker]
  obtain ⟨ι, hι, -⟩ :=
    RingHom.exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed χ (⊥ : Ideal κ) hQ
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ψ, F', inferInstance, inferInstance, ι, hψinj, hcomap, ?_, ?_⟩
  · have := (hmem (p : R)).mpr hpP
    rwa [map_natCast] at this
  · intro x
    have := congrArg (fun f : R →+* F' => f x) hι
    simp only [RingHom.comp_apply] at this
    exact this

end Main

end OrderCharLift

end

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R]
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p] (π : R →+* F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
        (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
        (ψ : R →+* O) (F' : Type) (_ : Field F') (_ : Algebra F F')
        (ι : IsLocalRing.ResidueField O →+* F'),
      Function.Injective ψ ∧
      Ideal.comap ψ (IsLocalRing.maximalIdeal O) = RingHom.ker π ∧
      (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      ∀ x, ι (IsLocalRing.residue O (ψ x)) = algebraMap F F' (π x) :=
  OrderCharLift.main R p π

end S_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int
end P2MW
export P2MW.S_exists_ringHom_completeDVR_residue_eq_of_moduleFinite_int (solution)
