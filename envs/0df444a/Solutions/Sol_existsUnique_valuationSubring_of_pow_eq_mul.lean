-- Prove2me | solution 1 for existsUnique_valuationSubring_of_pow_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/fa9c6eae-4192-55af-b738-81a91e917d05

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_existsUnique_valuationSubring_of_pow_eq_mul

set_option autoImplicit false

open IsLocalRing Module

theorem integralClosure_existsUnique_primesOver_of_pow_eq_mul
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (n : ℕ) (hn0 : 0 < n) (hn : finrank K L ≤ n)
    (π : R) (hπ : Irreducible π) (u v : L) (huv : u * v = 1) (hu : IsIntegral R u) (hv : IsIntegral R v)
    (ϖ : L) (hϖ : ϖ ^ n = algebraMap R L π * u) :
    finrank K L = n ∧
    ∃ P : Ideal ↥(integralClosure R L), P.IsMaximal ∧
      (maximalIdeal R).primesOver ↥(integralClosure R L) = {P} ∧
      Ideal.ramificationIdx' (maximalIdeal R) P = n ∧
      Ideal.inertiaDeg' (maximalIdeal R) P = 1 := by
  classical

  haveI : IsIntegralClosure ↥(integralClosure R L) R L := integralClosure.isIntegralClosure R L
  haveI hDed : IsDedekindDomain ↥(integralClosure R L) := IsIntegralClosure.isDedekindDomain R K L ↥(integralClosure R L)
  haveI hFin : Module.Finite R ↥(integralClosure R L) := IsIntegralClosure.finite R K L ↥(integralClosure R L)
  haveI : IsFractionRing ↥(integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L ↥(integralClosure R L)
  set S := integralClosure R L with hSdef
  set p := maximalIdeal R with hpdef
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpπ : p = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

  have hint : IsIntegral R ϖ := by
    refine IsIntegral.of_pow hn0 ?_
    rw [hϖ]; exact isIntegral_algebraMap.mul hu
  set ϖS : ↥S := ⟨ϖ, hint⟩ with hϖS
  set uS : ↥S := ⟨u, hu⟩ with huSdef
  have huS : IsUnit uS := isUnit_iff_exists_inv.mpr ⟨⟨v, hv⟩, Subtype.ext huv⟩
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_mul] at huv; exact zero_ne_one huv
  have hπS : algebraMap R ↥S π * uS = ϖS ^ n := by
    apply Subtype.ext
    show algebraMap R L π * u = ϖ ^ n
    rw [hϖ]
  have hmap : Ideal.map (algebraMap R ↥S) p = (Ideal.span {ϖS}) ^ n := by
    rw [hpπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    apply Ideal.span_singleton_eq_span_singleton.mpr
    rw [← hπS]
    exact associated_mul_unit_right _ _ huS
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hϖ0 : ϖS ≠ 0 := by
    intro h0
    have h1 : ϖ = 0 := congrArg Subtype.val h0
    have h2 : algebraMap R L π * u = 0 := by rw [← hϖ, h1, zero_pow hn0.ne']
    rcases mul_eq_zero.mp h2 with h | h
    · exact hπ.ne_zero (hRL (by rw [h, map_zero]))
    · exact hu0 h
  have hspan0 : Ideal.span {ϖS} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hmap0 : Ideal.map (algebraMap R ↥S) p ≠ ⊥ := by rw [hmap]; exact pow_ne_zero _ hspan0
  haveI : Module.IsTorsionFree R L :=
    ⟨fun r hr x y hxy => by
      have h0 : algebraMap R L r ≠ 0 := fun h => hr.ne_zero (hRL (by rw [h, map_zero]))
      simp only [Algebra.smul_def] at hxy
      exact mul_left_cancel₀ h0 hxy⟩
  haveI : Module.IsTorsionFree R ↥S := Subalgebra.instIsTorsionFree _

  have hprime_over : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥S, P.IsPrime ∧ P.LiesOver p := fun P hP =>
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 ↥S).mp hP
  have he : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥S, n ≤ Ideal.ramificationIdx' p P := by
    intro P hP
    obtain ⟨hPp, hPo⟩ := hprime_over P hP
    have hdvd : P ∣ Ideal.map (algebraMap R ↥S) p := Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr hPo.over.le)
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      exact hmap0 (le_bot_iff.mp (Ideal.le_of_dvd hdvd))
    have hPpr : Prime P := Ideal.prime_of_isPrime hP0 hPp
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hPp hP0, hmap,
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
    have hdvd1 : P ∣ Ideal.span {ϖS} := hPpr.dvd_of_dvd_pow (by rw [← hmap]; exact hdvd)
    obtain ⟨Q, hQ, hPQ⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hspan0 hPpr.irreducible hdvd1
    rw [associated_iff_eq] at hPQ
    subst hPQ
    have : 1 ≤ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS})).count P := Multiset.one_le_count_iff_mem.mpr hQ
    calc n = n * 1 := (mul_one n).symm
      _ ≤ n * _ := Nat.mul_le_mul_left n this
  have hf : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥S, 1 ≤ Ideal.inertiaDeg' p P := by
    intro P hP
    obtain ⟨hPp, hPo⟩ := hprime_over P hP
    haveI := hPp; haveI := hPo
    exact Ideal.inertiaDeg'_pos p P

  have hsum := Ideal.sum_ramification_inertia ↥S K L hp0
  have hne : (IsDedekindDomain.primesOverFinset p ↥S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    exact (Module.finrank_pos (R := K) (M := L)).ne' hsum.symm
  have hcard : (IsDedekindDomain.primesOverFinset p ↥S).card * n ≤ n := by
    calc (IsDedekindDomain.primesOverFinset p ↥S).card * n
        = ∑ P ∈ IsDedekindDomain.primesOverFinset p ↥S, n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p ↥S, Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P :=
          Finset.sum_le_sum fun P hP => by nlinarith [he P hP, hf P hP]
      _ = finrank K L := hsum
      _ ≤ n := hn
  have hcard1 : (IsDedekindDomain.primesOverFinset p ↥S).card = 1 := by
    have h1 : (IsDedekindDomain.primesOverFinset p ↥S).card ≤ 1 := by
      by_contra h; push Not at h
      have : 2 * n ≤ (IsDedekindDomain.primesOverFinset p ↥S).card * n := Nat.mul_le_mul_right n h
      omega
    have h2 := Finset.card_pos.mpr hne
    omega
  obtain ⟨P, hPeq⟩ := Finset.card_eq_one.mp hcard1
  have hPmem : P ∈ IsDedekindDomain.primesOverFinset p ↥S := by rw [hPeq]; exact Finset.mem_singleton_self P
  obtain ⟨hPp, hPo⟩ := hprime_over P hPmem
  have heP := he P hPmem
  have hfP := hf P hPmem
  rw [hPeq, Finset.sum_singleton] at hsum
  have hef : Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P ≤ n := hsum ▸ hn
  have hfP1 : Ideal.inertiaDeg' p P = 1 := by
    by_contra h
    have h2 : 2 ≤ Ideal.inertiaDeg' p P := by omega
    have : 2 * n ≤ Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P := by nlinarith
    omega
  have heP' : Ideal.ramificationIdx' p P = n := by
    rw [hfP1, mul_one] at hef; omega
  have hfin : finrank K L = n := by rw [← hsum, hfP1, mul_one, heP']
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hmap0 (le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr hPo.over.le))
  haveI := hPp
  refine ⟨hfin, P, Ideal.IsPrime.isMaximal hPp hP0, ?_, heP', hfP1⟩
  rw [← IsDedekindDomain.coe_primesOverFinset hp0 ↥S, hPeq, Finset.coe_singleton]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (n : ℕ) (hn0 : 0 < n) (hn : finrank K L ≤ n)
    (π : R) (hπ : Irreducible π) (u v : L) (huv : u * v = 1) (hu : IsIntegral R u) (hv : IsIntegral R v)
    (ϖ : L) (hϖ : ϖ ^ n = algebraMap R L π * u) :
    finrank K L = n ∧
    ∃ (W : ValuationSubring L) (hRW : ∀ r : R, algebraMap R L r ∈ W),
      (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      IsDiscreteValuationRing ↥W ∧
      (∃ hϖW : ϖ ∈ W, maximalIdeal ↥W = Ideal.span {(⟨ϖ, hϖW⟩ : ↥W)}) ∧
      (∀ w : ↥W, ∃ r : R, w - ⟨algebraMap R L r, hRW r⟩ ∈ maximalIdeal ↥W) ∧
      (∀ k : K, algebraMap K L k ∈ W ↔ ∃ r : R, algebraMap R K r = k) ∧
      (∀ (W' : ValuationSubring L) (hRW' : ∀ r : R, algebraMap R L r ∈ W'),
        (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W) := by
  classical
  obtain ⟨hfin, P, hPmax, hPover, heP, hfP⟩ :=
    integralClosure_existsUnique_primesOver_of_pow_eq_mul R K L n hn0 hn π hπ u v huv hu hv ϖ hϖ
  haveI : IsIntegralClosure ↥(integralClosure R L) R L := integralClosure.isIntegralClosure R L
  haveI hDed : IsDedekindDomain ↥(integralClosure R L) := IsIntegralClosure.isDedekindDomain R K L ↥(integralClosure R L)
  haveI hFin : Module.Finite R ↥(integralClosure R L) := IsIntegralClosure.finite R K L ↥(integralClosure R L)
  haveI : IsFractionRing ↥(integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R K L ↥(integralClosure R L)
  haveI := hPmax
  haveI hPprime : P.IsPrime := hPmax.isPrime
  have hp0 : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hPmem : P ∈ (maximalIdeal R).primesOver ↥(integralClosure R L) := by rw [hPover]; exact Set.mem_singleton P
  haveI hPo : P.LiesOver (maximalIdeal R) := hPmem.2
  have hP0 : P ≠ ⊥ := by
    intro h
    have : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≤ P := Ideal.map_le_iff_le_comap.mpr hPo.over.le
    rw [h, le_bot_iff, Ideal.map_eq_bot_iff_of_injective] at this
    · exact hp0 this
    · intro a b hab
      exact hRL (congrArg Subtype.val hab)

  haveI : IsDomain (Localization.AtPrime P) := IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  have hSL : Function.Injective (algebraMap ↥(integralClosure R L) L) := Subtype.val_injective
  have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap ↥(integralClosure R L) L y) := by
    intro y
    apply IsUnit.mk0
    intro h0
    have hy0 : (y : ↥(integralClosure R L)) = 0 := hSL (by rw [h0]; simp)
    exact y.2 (by rw [hy0]; exact P.zero_mem)
  letI algAL : Algebra (Localization.AtPrime P) L := (IsLocalization.lift (M := P.primeCompl) hunits).toAlgebra
  have halgAL : ∀ s : ↥(integralClosure R L), algebraMap (Localization.AtPrime P) L (algebraMap ↥(integralClosure R L) (Localization.AtPrime P) s) = (s : L) :=
    fun s => IsLocalization.lift_eq hunits s
  haveI : IsScalarTower ↥(integralClosure R L) (Localization.AtPrime P) L := IsScalarTower.of_algebraMap_eq fun s => (halgAL s).symm
  haveI : IsFractionRing (Localization.AtPrime P) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl (Localization.AtPrime P) L
  have hAL : Function.Injective (algebraMap (Localization.AtPrime P) L) := IsFractionRing.injective (Localization.AtPrime P) L
  haveI hDVRA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥(integralClosure R L) hP0 (Localization.AtPrime P)

  set W : ValuationSubring L := (ValuationRing.valuation (Localization.AtPrime P) L).valuationSubring with hWdef
  have hmemW : ∀ x : L, x ∈ W ↔ ∃ a : Localization.AtPrime P, algebraMap (Localization.AtPrime P) L a = x := by
    intro x
    rw [hWdef, Valuation.mem_valuationSubring_iff, ← Valuation.mem_integer_iff]
    exact ValuationRing.mem_integer_iff (Localization.AtPrime P) L x
  let f : Localization.AtPrime P →+* ↥W :=
    { toFun := fun a => ⟨algebraMap (Localization.AtPrime P) L a, (hmemW _).mpr ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  have hf_apply : ∀ a, ((f a : ↥W) : L) = algebraMap (Localization.AtPrime P) L a := fun a => rfl
  have hfbij : Function.Bijective f := by
    refine ⟨fun a b hab => hAL (by rw [← hf_apply, ← hf_apply, hab]), fun w => ?_⟩
    obtain ⟨a, ha⟩ := (hmemW (w : L)).mp w.2
    exact ⟨a, Subtype.ext ha⟩
  let eAW : Localization.AtPrime P ≃+* ↥W := RingEquiv.ofBijective f hfbij
  have heAW : ∀ a, ((eAW a : ↥W) : L) = algebraMap (Localization.AtPrime P) L a := fun a => rfl
  have hSW : ∀ s : ↥(integralClosure R L), (s : L) ∈ W := fun s => (hmemW _).mpr ⟨algebraMap ↥(integralClosure R L) _ s, halgAL s⟩
  have heAWS : ∀ s : ↥(integralClosure R L), eAW (algebraMap ↥(integralClosure R L) (Localization.AtPrime P) s) = ⟨(s : L), hSW s⟩ :=
    fun s => Subtype.ext (by rw [heAW, halgAL])
  have hRW : ∀ r : R, algebraMap R L r ∈ W := fun r => by
    have : algebraMap R L r = ((algebraMap R ↥(integralClosure R L) r : ↥(integralClosure R L)) : L) := rfl
    rw [this]; exact hSW _

  haveI : IsPrincipalIdealRing ↥W := IsPrincipalIdealRing.of_surjective (eAW : Localization.AtPrime P →+* ↥W) eAW.surjective
  have hunitW : ∀ a : Localization.AtPrime P, IsUnit (eAW a) ↔ IsUnit a :=
    fun a => ⟨fun h => by simpa using h.map eAW.symm, fun h => h.map eAW⟩
  have hmemmaxW : ∀ a : Localization.AtPrime P, eAW a ∈ maximalIdeal ↥W ↔ a ∈ maximalIdeal (Localization.AtPrime P) := by
    intro a; rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hunitW]
  have hSmax : ∀ s : ↥(integralClosure R L), (⟨(s : L), hSW s⟩ : ↥W) ∈ maximalIdeal ↥W ↔ s ∈ P := by
    intro s
    rw [← heAWS, hmemmaxW]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P s

  have hcentre : ∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro r hr
    have : (⟨algebraMap R L r, hRW r⟩ : ↥W) = ⟨((algebraMap R ↥(integralClosure R L) r : ↥(integralClosure R L)) : L), hSW _⟩ := rfl
    rw [this, hSmax]
    exact hPo.over.le hr |> fun h => (Ideal.mem_comap.mp h)

  have hπW : (⟨algebraMap R L π, hRW π⟩ : ↥W) ∈ maximalIdeal ↥W :=
    hcentre π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
  have hπW0 : (⟨algebraMap R L π, hRW π⟩ : ↥W) ≠ 0 := by
    intro h
    exact hπ.ne_zero (hRL (by rw [map_zero]; exact congrArg Subtype.val h))
  have hDVRW : IsDiscreteValuationRing ↥W :=
    { toIsPrincipalIdealRing := inferInstance
      toIsLocalRing := inferInstance
      not_a_field' := by
        intro hbot
        have := hπW
        rw [hbot, Ideal.mem_bot] at this
        exact hπW0 this }

  have hresK : ∀ k : K, algebraMap K L k ∈ W ↔ ∃ r : R, algebraMap R K r = k := by
    intro k
    constructor
    · intro hk
      rcases ValuationRing.isInteger_or_isInteger R k with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨r, hr⟩
      · by_cases hk0 : k = 0
        · exact ⟨0, by rw [hk0, map_zero]⟩
        by_cases hru : IsUnit r
        · obtain ⟨v, rfl⟩ := hru
          refine ⟨((v⁻¹ : Rˣ) : R), ?_⟩
          have h1 : algebraMap R K ((v⁻¹ : Rˣ) : R) * algebraMap R K (v : R) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [hr] at h1
          calc algebraMap R K ((v⁻¹ : Rˣ) : R) = algebraMap R K ((v⁻¹ : Rˣ) : R) * (k⁻¹ * k) := by
                rw [inv_mul_cancel₀ hk0, mul_one]
            _ = k := by rw [← mul_assoc, h1, one_mul]
        · exfalso
          have hrm : r ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hru
          have h1 : (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W := hcentre r hrm
          have h2 : algebraMap R L r * algebraMap K L k = 1 := by
            rw [IsScalarTower.algebraMap_apply R K L, hr, ← map_mul, inv_mul_cancel₀ hk0, map_one]
          have hunit : IsUnit (⟨algebraMap R L r, hRW r⟩ : ↥W) :=
            isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L k, hk⟩, Subtype.ext h2⟩
          exact (IsLocalRing.mem_maximalIdeal _).mp h1 hunit
    · rintro ⟨r, rfl⟩
      rw [← IsScalarTower.algebraMap_apply]
      exact hRW r

  have hmemWfrac : ∀ x : L, x ∈ W ↔ ∃ (s : ↥(integralClosure R L)) (t : ↥(integralClosure R L)), t ∉ P ∧ x * (t : L) = (s : L) := by
    intro x
    rw [hmemW]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
      refine ⟨s, t, t.2, ?_⟩
      rw [← halgAL t, ← map_mul, IsLocalization.mk'_spec, halgAL]
    · rintro ⟨s, t, ht, hx⟩
      refine ⟨IsLocalization.mk' _ s (⟨t, ht⟩ : P.primeCompl), ?_⟩
      have ht0 : (t : L) ≠ 0 := fun h => ht (by rw [show t = 0 from Subtype.ext h]; exact P.zero_mem)
      apply mul_right_cancel₀ ht0
      rw [hx, ← halgAL t, ← map_mul]
      show algebraMap _ L (IsLocalization.mk' (Localization.AtPrime P) s (⟨t, ht⟩ : P.primeCompl) * algebraMap _ _ ((⟨t, ht⟩ : P.primeCompl) : ↥(integralClosure R L))) = _
      rw [IsLocalization.mk'_spec, halgAL]
  have huniq : ∀ (W' : ValuationSubring L) (hRW' : ∀ r : R, algebraMap R L r ∈ W'),
      (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W := by
    intro W' hRW' hcen'

    have hSW' : ∀ s : ↥(integralClosure R L), (s : L) ∈ W' := by
      intro s
      have hsint : IsIntegral R (s : L) := s.2
      letI : Algebra R ↥W' := ((algebraMap R L).codRestrict W'.toSubring hRW').toAlgebra
      haveI : IsScalarTower R ↥W' L := IsScalarTower.of_algebraMap_eq fun r => rfl
      have hsint' : IsIntegral ↥W' (s : L) := hsint.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W') (K := L)).mp hsint'
      rw [← hy]; exact y.2

    let ι' : ↥(integralClosure R L) →+* ↥W' := (integralClosure R L).val.toRingHom.codRestrict W'.toSubring hSW'
    let Q : Ideal ↥(integralClosure R L) := (maximalIdeal ↥W').comap ι'
    have hQmem : ∀ s : ↥(integralClosure R L), s ∈ Q ↔ (⟨(s : L), hSW' s⟩ : ↥W') ∈ maximalIdeal ↥W' := fun s => Iff.rfl
    haveI hQprime : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQne : Q.comap (algebraMap R ↥(integralClosure R L)) ≠ ⊤ := by
      rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_comap, map_one, hQmem]
      intro h1
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 ⟨⟨⟨_, hSW' 1⟩, ⟨_, hSW' 1⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    have hQle : maximalIdeal R ≤ Q.comap (algebraMap R ↥(integralClosure R L)) := by
      intro r hr
      rw [Ideal.mem_comap, hQmem]
      exact hcen' r hr
    haveI hQover : Q.LiesOver (maximalIdeal R) := ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hQne hQle⟩
    have hQP : Q = P := by
      have : Q ∈ (maximalIdeal R).primesOver ↥(integralClosure R L) := ⟨hQprime, hQover⟩
      rw [hPover] at this
      exact this

    have hWW' : W ≤ W' := by
      intro x hx
      obtain ⟨s, t, ht, hxt⟩ := (hmemWfrac x).mp hx
      have htQ : t ∉ Q := by rw [hQP]; exact ht
      have htunit : IsUnit (⟨(t : L), hSW' t⟩ : ↥W') := by
        by_contra h
        exact htQ ((hQmem t).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
      have ht0 : (t : L) ≠ 0 := fun h => ht (by rw [show t = 0 from Subtype.ext h]; exact P.zero_mem)
      have hx' : x = (s : L) * (t : L)⁻¹ := by rw [← hxt, mul_inv_cancel_right₀ ht0]
      rw [hx']
      refine mul_mem (hSW' s) ?_
      have hv : W'.valuation (t : L) = 1 := (W'.valuation_eq_one_iff ⟨(t : L), hSW' t⟩).mp htunit
      apply (W'.valuation_le_one_iff _).mp
      rw [map_inv₀, hv, inv_one]

    set J := W.idealOfLE W' hWW' with hJdef
    have hJmem : ∀ w : ↥W, w ∈ J ↔ (⟨(w : L), hWW' w.2⟩ : ↥W') ∈ maximalIdeal ↥W' := fun w => Iff.rfl
    haveI : J.IsPrime := ValuationSubring.prime_idealOfLE W W' hWW'
    have hJ0 : J ≠ ⊥ := by
      intro hJ0
      have hπJ : (⟨algebraMap R L π, hRW π⟩ : ↥W) ∈ J := by
        rw [hJmem]
        exact hcen' π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      rw [hJ0, Ideal.mem_bot] at hπJ
      exact hπW0 hπJ
    have hJmax : J = maximalIdeal ↥W := IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hJ0)
    apply le_antisymm _ hWW'
    intro x hx'
    by_contra hxW
    have hxinv : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hxW
    have hx0 : x ≠ 0 := fun h => hxW (h ▸ W.zero_mem)

    have hxm : (⟨x⁻¹, hxinv⟩ : ↥W) ∈ maximalIdeal ↥W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
      have hb' : x⁻¹ * (b : L) = 1 := congrArg Subtype.val hb
      have : (b : L) = x := by
        have := congrArg (fun z => x * z) hb'
        simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at this
        exact this
      exact hxW (this ▸ b.2)
    rw [← hJmax, hJmem] at hxm
    have hu' : IsUnit (⟨x⁻¹, hWW' hxinv⟩ : ↥W') :=
      isUnit_iff_exists_inv.mpr ⟨⟨x, hx'⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hxm hu'

  have hint : IsIntegral R ϖ := by
    refine IsIntegral.of_pow hn0 ?_
    rw [hϖ]; exact isIntegral_algebraMap.mul hu
  set ϖS : ↥(integralClosure R L) := ⟨ϖ, hint⟩ with hϖS
  set uS : ↥(integralClosure R L) := ⟨u, hu⟩ with huSdef
  have huS : IsUnit uS := isUnit_iff_exists_inv.mpr ⟨⟨v, hv⟩, Subtype.ext huv⟩
  have hu0 : u ≠ 0 := fun h => by rw [h, zero_mul] at huv; exact zero_ne_one huv
  have hπS : algebraMap R ↥(integralClosure R L) π * uS = ϖS ^ n := by
    apply Subtype.ext
    show algebraMap R L π * u = ϖ ^ n
    rw [hϖ]
  have hmap : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) = (Ideal.span {ϖS}) ^ n := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    apply Ideal.span_singleton_eq_span_singleton.mpr
    rw [← hπS]
    exact associated_mul_unit_right _ _ huS
  have hϖ0 : ϖS ≠ 0 := by
    intro h0
    have h1 : ϖ = 0 := congrArg Subtype.val h0
    have h2 : algebraMap R L π * u = 0 := by rw [← hϖ, h1, zero_pow hn0.ne']
    rcases mul_eq_zero.mp h2 with h | h
    · exact hπ.ne_zero (hRL (by rw [h, map_zero]))
    · exact hu0 h
  have hspan0 : Ideal.span {ϖS} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hmap0 : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≠ ⊥ := by rw [hmap]; exact pow_ne_zero _ hspan0
  have hPpr : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  have hdvdP : P ∣ Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr hPo.over.le)

  have hfac : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS}), Q = P := by
    intro Q hQ
    have hQpr : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    have hQdvd : Q ∣ Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) := by
      rw [hmap]; exact dvd_pow (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ) hn0.ne'
    have hQ0 : Q ≠ ⊥ := hQpr.ne_zero
    haveI hQprime : Q.IsPrime := Ideal.isPrime_of_prime hQpr
    have hQle : Ideal.map (algebraMap R ↥(integralClosure R L)) (maximalIdeal R) ≤ Q := Ideal.le_of_dvd hQdvd
    have hQne : Q.comap (algebraMap R ↥(integralClosure R L)) ≠ ⊤ := by
      rw [Ne, Ideal.comap_eq_top_iff]; exact hQprime.ne_top
    haveI : Q.LiesOver (maximalIdeal R) :=
      ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hQne (Ideal.map_le_iff_le_comap.mp hQle)⟩
    have : Q ∈ (maximalIdeal R).primesOver ↥(integralClosure R L) := ⟨hQprime, inferInstance⟩
    rw [hPover] at this
    exact this
  have hcount : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS})).count P = 1 := by
    have h1 := heP
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hPprime hP0, hmap,
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul] at h1
    have : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS})).count P * n = 1 * n := by rw [one_mul, mul_comm]; exact h1
    exact Nat.eq_of_mul_eq_mul_right hn0 this
  have hnf : UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ϖS}) = {P} := by
    have hrep := Multiset.eq_replicate_of_mem hfac
    rw [hrep, Multiset.count_replicate_self] at hcount
    rw [hrep, hcount, Multiset.replicate_one]
  have hspanP : Ideal.span {ϖS} = P := by
    have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hspan0
    rw [hnf, Multiset.prod_singleton] at hassoc
    exact (associated_iff_eq.mp hassoc).symm
  have hϖW : ϖ ∈ W := hSW ϖS
  have hmaxW : maximalIdeal ↥W = Ideal.span {(⟨ϖ, hϖW⟩ : ↥W)} := by
    have hmaxA : maximalIdeal (Localization.AtPrime P) = Ideal.span {algebraMap ↥(integralClosure R L) (Localization.AtPrime P) ϖS} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal,
        ← congrArg (Ideal.map (algebraMap ↥(integralClosure R L) (Localization.AtPrime P))) hspanP,
        Ideal.map_span, Set.image_singleton]
    apply le_antisymm
    · intro w hw
      have h1 : eAW.symm w ∈ maximalIdeal (Localization.AtPrime P) := by
        rw [← hmemmaxW, RingEquiv.apply_symm_apply]; exact hw
      rw [hmaxA, Ideal.mem_span_singleton] at h1
      obtain ⟨c, hc⟩ := h1
      rw [Ideal.mem_span_singleton]
      refine ⟨eAW c, ?_⟩
      have : w = eAW (eAW.symm w) := (RingEquiv.apply_symm_apply eAW w).symm
      rw [this, hc, map_mul, heAWS]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show (⟨ϖ, hϖW⟩ : ↥W) ∈ maximalIdeal ↥W
      have : (⟨ϖ, hϖW⟩ : ↥W) = ⟨((ϖS : ↥(integralClosure R L)) : L), hSW ϖS⟩ := rfl
      rw [this, hSmax, ← hspanP]
      exact Ideal.mem_span_singleton_self ϖS

  have hresS : ∀ s : ↥(integralClosure R L), ∃ r : R, s - algebraMap R _ r ∈ P := by
    intro s
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    have hf1 : Module.finrank (R ⧸ maximalIdeal R) (↥(integralClosure R L) ⧸ P) = 1 := by
      rw [← Ideal.inertiaDeg_algebraMap]; exact hfP
    have h1 : (1 : ↥(integralClosure R L) ⧸ P) ≠ 0 := by
      rw [Ne, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
      exact hPprime.ne_top ∘ (Ideal.eq_top_iff_one P).mpr
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := R ⧸ maximalIdeal R) (1 : ↥(integralClosure R L) ⧸ P) h1).mp hf1 (Ideal.Quotient.mk P s)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨r, ?_⟩
    rw [← Ideal.Quotient.eq, ← hc, Algebra.smul_def, mul_one]
    rfl
  have hres : ∀ w : ↥W, ∃ r : R, w - ⟨algebraMap R L r, hRW r⟩ ∈ maximalIdeal ↥W := by
    intro w
    obtain ⟨s, t, ht, hwt⟩ := (hmemWfrac (w : L)).mp w.2
    obtain ⟨rt, hrt⟩ := hresS t
    obtain ⟨rs, hrs⟩ := hresS s
    have hrtu : IsUnit rt := by
      by_contra h
      have hrtm : algebraMap R ↥(integralClosure R L) rt ∈ P := hPo.over.le ((IsLocalRing.mem_maximalIdeal _).mpr h)
      exact ht (by simpa using P.add_mem hrt hrtm)
    obtain ⟨v, hv⟩ := hrtu
    refine ⟨rs * ((v⁻¹ : Rˣ) : R), ?_⟩

    have ht0 : (t : L) ≠ 0 := fun h => ht (by rw [show t = 0 from Subtype.ext h]; exact P.zero_mem)
    have htunitW : IsUnit (⟨(t : L), hSW t⟩ : ↥W) := by
      by_contra h
      exact ht ((hSmax t).mp ((IsLocalRing.mem_maximalIdeal _).mpr h))
    have hvv : algebraMap R ↥(integralClosure R L) (v : R) * algebraMap R ↥(integralClosure R L) ((v⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hnum : s - t * algebraMap R _ (rs * ((v⁻¹ : Rˣ) : R)) ∈ P := by
      have e1 : s - t * algebraMap R _ (rs * ((v⁻¹ : Rˣ) : R)) =
          (s - algebraMap R _ rs) - (t - algebraMap R _ rt) * algebraMap R _ (rs * ((v⁻¹ : Rˣ) : R)) := by
        rw [← hv, map_mul]
        linear_combination (-(algebraMap R ↥(integralClosure R L) rs)) * hvv
      rw [e1]
      exact P.sub_mem hrs (P.mul_mem_right _ hrt)
    have hprod : (w - ⟨algebraMap R L (rs * ((v⁻¹ : Rˣ) : R)), hRW _⟩) * ⟨(t : L), hSW t⟩ =
        (⟨((s - t * algebraMap R ↥(integralClosure R L) (rs * ((v⁻¹ : Rˣ) : R)) : ↥(integralClosure R L)) : L), hSW _⟩ : ↥W) := by
      apply Subtype.ext
      show ((w : L) - algebraMap R L (rs * ((v⁻¹ : Rˣ) : R))) * (t : L) = _
      rw [sub_mul, hwt]
      push_cast
      simp only [Algebra.cast, map_mul]
      ring
    have hmem : (w - ⟨algebraMap R L (rs * ((v⁻¹ : Rˣ) : R)), hRW _⟩) * ⟨(t : L), hSW t⟩ ∈ maximalIdeal ↥W := by
      rw [hprod, hSmax]; exact hnum
    exact (Ideal.mul_unit_mem_iff_mem _ htunitW).mp hmem
  exact ⟨hfin, W, hRW, hcentre, hDVRW, ⟨hϖW, hmaxW⟩, hres, hresK, huniq⟩

end S_existsUnique_valuationSubring_of_pow_eq_mul
end P2MW
export P2MW.S_existsUnique_valuationSubring_of_pow_eq_mul (solution)
