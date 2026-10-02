-- Prove2me | solution 2 for flt5_zz5_kummer_pid_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:42:51.790754+00:00
-- url     : https://prove2.me/submissions/68a0dfe3-b0c0-4d12-bc9f-9c8fa6c609b3

import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

set_option autoImplicit false

namespace Flt5PidRoot4202

open NumberField Ideal

abbrev K5 := CyclotomicField 5 ℚ

instance cyc5 : IsCyclotomicExtension {5} ℚ K5 := CyclotomicField.isCyclotomicExtension 5 ℚ

instance galois5 : IsGalois ℚ K5 := IsCyclotomicExtension.isGalois {5} ℚ K5

instance totCx5 : IsTotallyComplex K5 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 5) K5 (by norm_num)

lemma prod_conj_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ι)
    (hτ : ∀ i, τ (τ i) = i) (hfix : ∀ i, τ i ≠ i) (f : ι → ℂ)
    (hf : ∀ i, f (τ i) = (starRingEnd ℂ) (f i)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∏ i, f i = (r : ℂ) := by
  suffices H : ∀ s : Finset ι, (∀ i ∈ s, τ i ∈ s) →
      ∃ r : ℝ, 0 ≤ r ∧ ∏ i ∈ s, f i = (r : ℂ) from H Finset.univ (by simp)
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · exact ⟨1, zero_le_one, by simp⟩
    · have hti : τ i ∈ s.erase i := Finset.mem_erase.mpr ⟨hfix i, hs i hi⟩
      have htsub : (s.erase i).erase (τ i) ⊂ s :=
        lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hi)
      have htst : ∀ j ∈ (s.erase i).erase (τ i), τ j ∈ (s.erase i).erase (τ i) := by
        intro j hj
        simp only [Finset.mem_erase] at hj ⊢
        refine ⟨?_, ?_, hs j hj.2.2⟩
        · intro h
          apply hj.2.1
          calc j = τ (τ j) := (hτ j).symm
            _ = τ (τ i) := by rw [h]
            _ = i := hτ i
        · intro h
          apply hj.1
          calc j = τ (τ j) := (hτ j).symm
            _ = τ i := by rw [h]
      obtain ⟨r, hr0, hr⟩ := ih _ htsub htst
      refine ⟨Complex.normSq (f i) * r, mul_nonneg (Complex.normSq_nonneg _) hr0, ?_⟩
      rw [← Finset.mul_prod_erase s f hi, ← Finset.mul_prod_erase (s.erase i) f hti, hr, hf,
        ← mul_assoc, Complex.mul_conj]
      push_cast
      ring

lemma normQ_nonneg (x : K5) : 0 ≤ Algebra.norm ℚ x := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K5 ℂ) (fun φ => φ x) (fun σ => σ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  obtain ⟨r, hr0, hr⟩ := prod_conj_nonneg (fun φ : K5 →+* ℂ => ComplexEmbedding.conjugate φ)
    (fun φ => star_star φ)
    (fun φ hφ => IsTotallyComplex.complexEmbedding_not_isReal φ
      (ComplexEmbedding.isReal_iff.mpr hφ))
    (fun φ => φ x) (fun φ => ComplexEmbedding.conjugate_coe_eq φ x)
  rw [hr] at h
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℝ) = r := by
    have := congrArg Complex.re h
    simpa using this
  have : (0 : ℝ) ≤ ((Algebra.norm ℚ x : ℚ) : ℝ) := h2 ▸ hr0
  exact_mod_cast this

lemma normZ_nonneg (x : 𝓞 K5) : 0 ≤ Algebra.norm ℤ x := by
  have h := normQ_nonneg (x : K5)
  rw [← Algebra.coe_norm_int] at h
  exact_mod_cast h

noncomputable def g (p : ℕ) : ℕ := (span {(p : ℤ)} : Ideal ℤ).inertiaDegIn (𝓞 K5)

lemma absNorm_of_liesOver (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K5)) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})] : absNorm P = p ^ g p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  rw [absNorm_eq_pow_inertiaDeg' P hp, inertiaDeg'_eq_inertiaDeg, g,
    inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(K5/ℚ)]

lemma g_dvd_four (p : ℕ) (hp : p.Prime) : g p ∣ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 K5)
    Gal(K5/ℚ)
  have hcard : Nat.card Gal(K5/ℚ) = 4 := by
    rw [IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank K5 (Polynomial.cyclotomic.irreducible_rat (n := 5) (by norm_num))]
    decide
  rw [hcard] at h
  rw [g, ← h]
  exact (dvd_mul_left _ _).mul_left _

lemma g_dvd (p : ℕ) (hp : p.Prime) (A : Ideal (𝓞 K5)) :
    g p ∣ (absNorm A).factorization p := by
  induction A using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx]
    simp
  | h₃ a P ha hP ih =>
    rw [map_mul]
    by_cases h0 : absNorm a = 0
    · simp [h0]
    haveI : P.IsPrime := Ideal.isPrime_of_prime hP
    haveI : NeZero P := ⟨hP.ne_zero⟩
    have hq : (absNorm (under ℤ P)).Prime := Nat.absNorm_under_prime P
    have hPq := absNorm_of_liesOver _ hq P
    rw [hPq, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) h0, Finsupp.add_apply,
      Nat.factorization_pow, hq.factorization]
    refine dvd_add ?_ ih
    by_cases hpq : absNorm (under ℤ P) = p
    · rw [hpq]; simp
    · simp [hpq]

lemma exists_ideal_norm (n : ℕ) (hn : n ≠ 0) (I : Ideal (𝓞 K5)) (hI : absNorm I = n ^ 5) :
    ∃ J : Ideal (𝓞 K5), absNorm J = n := by
  classical
  have hP : ∀ p : ℕ, p.Prime → ∃ P : Ideal (𝓞 K5), absNorm P = p ^ g p := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 K5)))
    exact ⟨P, absNorm_of_liesOver p hp P⟩
  choose! Pf hPf using hP
  have hdiv : ∀ p, p.Prime → g p ∣ n.factorization p := by
    intro p hp
    have h1 := g_dvd p hp I
    rw [hI, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h1
    have hcop : Nat.Coprime (g p) 5 :=
      Nat.Coprime.coprime_dvd_left (g_dvd_four p hp) (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h1
  refine ⟨∏ p ∈ n.primeFactors, Pf p ^ (n.factorization p / g p), ?_⟩
  rw [map_prod]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [map_pow, hPf p hpp, ← pow_mul, Nat.mul_div_cancel' (hdiv p hpp)]

end Flt5PidRoot4202

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  rcases eq_or_ne s 0 with rfl | hs
  · exact ⟨0, by simp⟩
  have hs0 : 0 ≤ s := by
    have h := Flt5PidRoot4202.normZ_nonneg β
    rw [hβ] at h
    exact (Odd.pow_nonneg_iff (by decide)).mp h
  obtain ⟨J, hJ⟩ := Flt5PidRoot4202.exists_ideal_norm s.natAbs (Int.natAbs_ne_zero.mpr hs)
    (Ideal.span {β}) (by rw [Ideal.absNorm_span_singleton, hβ, Int.natAbs_pow])
  obtain ⟨d, hd⟩ := (hPID.principal J).principal
  refine ⟨d, ?_⟩
  have h1 : (Algebra.norm ℤ d).natAbs = s.natAbs := by
    rw [← Ideal.absNorm_span_singleton, ← hJ]
    exact congrArg _ hd.symm
  have h2 : Algebra.norm ℤ d = s := by
    rw [← Int.natAbs_of_nonneg (Flt5PidRoot4202.normZ_nonneg d), ← Int.natAbs_of_nonneg hs0, h1]
  rw [h2]
