-- Prove2me | solution 2 for flt5_zz5_fifth_root_norm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:17:36.22315+00:00
-- url     : https://prove2.me/submissions/1e080489-89c6-4f46-9066-55d3d3b235da

import Mathlib

open NumberField

namespace Eafb

instance instNZ5 : NeZero ((5:ℕ):ℚ) := ⟨by norm_num⟩

instance instCyc5 : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

theorem conj_ne (σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ) :
    (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp σ ≠ σ := by
  intro h
  have hz := IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  set z := IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)
  have hσ : IsPrimitiveRoot (σ z) 5 := hz.map_of_injective (f := σ) σ.injective
  have h1 : (starRingEnd ℂ) (σ z) = σ z := by
    have := congrArg (fun τ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ => τ z) h
    simpa using this
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h1
  have h5 : r ^ 5 = (1:ℝ) := by
    have := hσ.pow_eq_one
    rw [hr] at this
    exact_mod_cast this
  have hr1 : r = 1 :=
    (Odd.strictMono_pow (R := ℝ) (by decide : Odd 5)).injective (h5.trans (one_pow 5).symm)
  apply hσ.ne_one (by norm_num)
  rw [hr, hr1]; simp

theorem norm_nonneg_K (x : (CyclotomicField 5 ℚ)) : 0 ≤ Algebra.norm ℚ x := by
  by_cases hx : x = 0
  · subst hx; simp
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  set c : ((CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ) → ((CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ) :=
    fun σ => (Complex.conjAe.toAlgHom.restrictScalars ℚ).comp σ with hc
  have hcx : ∀ σ, c σ x = (starRingEnd ℂ) (σ x) := fun σ => by simp [hc]
  have hne : ∀ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, σ x ≠ 0 := fun σ => by
    intro h0; apply hx; exact σ.injective (by simpa using h0)
  have hnorm : ∀ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, (‖σ x‖ : ℂ) ≠ 0 := fun σ => by
    simpa using hne σ
  have hinv : ∏ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, (σ x / (‖σ x‖ : ℂ)) = 1 := by
    apply Finset.prod_ninvolution c
    · intro σ
      rw [hcx, Complex.norm_conj]
      rw [div_mul_div_comm, Complex.mul_conj, ← Complex.sq_norm]
      have := hnorm σ
      field_simp
      push_cast; ring
    · intro σ _; exact conj_ne σ
    · intro σ; simp
    · intro σ; ext y; simp [hc]
  have hprod : ∏ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, σ x = ((∏ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, ‖σ x‖ : ℝ) : ℂ) := by
    have : ∀ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, σ x = (‖σ x‖ : ℂ) * (σ x / (‖σ x‖ : ℂ)) := fun σ => by
      field_simp [hnorm σ]
    rw [Finset.prod_congr rfl (fun σ _ => this σ), Finset.prod_mul_distrib, hinv, mul_one]
    push_cast; rfl
  rw [hprod] at h
  have h2 : ((Algebra.norm ℚ x : ℝ) : ℂ) = ((∏ σ : (CyclotomicField 5 ℚ) →ₐ[ℚ] ℂ, ‖σ x‖ : ℝ) : ℂ) := by
    rw [← h]; simp
  have h3 := Complex.ofReal_injective h2
  have : (0:ℝ) ≤ (Algebra.norm ℚ x : ℝ) := by
    rw [h3]; exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  exact_mod_cast this

theorem norm_int_nonneg (x : 𝓞 (CyclotomicField 5 ℚ)) : 0 ≤ Algebra.norm ℤ x := by
  have := norm_nonneg_K (x : (CyclotomicField 5 ℚ))
  rw [← Algebra.coe_norm_int] at this
  exact_mod_cast this


open Ideal

noncomputable def fdeg (p : ℕ) : ℕ := if p = 5 then 1 else orderOf (p : ZMod 5)

theorem fdeg_coprime (p : ℕ) (hp : p.Prime) : Nat.Coprime (fdeg p) 5 := by
  unfold fdeg
  split_ifs with h5
  · norm_num
  · have h0 : (p : ZMod 5) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact h5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hd : orderOf (p : ZMod 5) ∣ 4 := ZMod.orderOf_dvd_card_sub_one h0
    exact Nat.Coprime.coprime_dvd_left hd (by norm_num)

theorem inertia_eq (p : ℕ) [hp : Fact p.Prime] (P : Ideal (𝓞 (CyclotomicField 5 ℚ)))
    [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    absNorm P = p ^ fdeg p := by
  rw [absNorm_eq_pow_inertiaDeg' P hp.out]
  congr 1
  have hPne : P ≠ ⊥ := by
    intro h
    have := Ideal.over_def P (span {(p : ℤ)})
    rw [h] at this
    have h2 : (span {(p : ℤ)} : Ideal ℤ) = ⊥ := by
      rw [this]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ _)
    rw [span_singleton_eq_bot] at h2
    exact hp.out.ne_zero (by exact_mod_cast h2)
  have : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  rw [inertiaDeg'_eq_inertiaDeg]
  unfold fdeg
  split_ifs with h5
  · subst h5
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 5 (CyclotomicField 5 ℚ) P
  · have hm : ¬ p ∣ 5 := by
      intro h
      exact h5 ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h)
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p (CyclotomicField 5 ℚ) P hm

theorem absNorm_prime (P : Ideal (𝓞 (CyclotomicField 5 ℚ))) [hPp : P.IsPrime] (hP : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ absNorm P = p ^ fdeg p := by
  have : NeZero P := ⟨hP⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = absNorm (under ℤ P) := ⟨_, rfl⟩
  have hp : p.Prime := hpdef ▸ Nat.absNorm_under_prime P
  have : Fact p.Prime := ⟨hp⟩
  have : P.LiesOver (span {(p : ℤ)}) := hpdef ▸ Int.liesOver_span_absNorm P
  exact ⟨p, hp, inertia_eq p P⟩

theorem exists_over (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 (CyclotomicField 5 ℚ)), absNorm P = p ^ fdeg p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPm, hPl⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (CyclotomicField 5 ℚ))
      (span {(p : ℤ)})
  exact ⟨P, inertia_eq p P⟩

def Good (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → fdeg p ∣ n.factorization p

theorem good_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h1 : Good a) (h2 : Good b) :
    Good (a * b) := by
  intro p hp
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  exact dvd_add (h1 p hp) (h2 p hp)

theorem good_prime_pow (q : ℕ) (hq : q.Prime) : Good (q ^ fdeg q) := by
  intro p hp
  rw [hq.factorization_pow]
  by_cases h : p = q
  · subst h; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm h)]; exact dvd_zero _

theorem good_absNorm (I : Ideal (𝓞 (CyclotomicField 5 ℚ))) (hI : I ≠ ⊥) :
    Good (absNorm I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ u hu =>
    rw [Ideal.isUnit_iff.mp hu, absNorm_top]
    intro p _; simp
  | h₃ a P ha hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have ha0 : a ≠ ⊥ := by
      intro h; apply hI; rw [h]; exact mul_bot P
    have : P.IsPrime := Ideal.isPrime_of_prime hP
    obtain ⟨p, hp, hn⟩ := absNorm_prime P hP0
    rw [map_mul, hn]
    refine good_mul (pow_ne_zero _ hp.ne_zero) ?_ (good_prime_pow p hp) (ih ha0)
    exact (absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero ha0)

theorem good_of_pow5 (n : ℕ) (h : Good (n ^ 5)) : Good n := by
  intro p hp
  have := h p hp
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this
  exact (fdeg_coprime p hp).dvd_of_dvd_mul_left this

theorem exists_of_good (n : ℕ) (hn : n ≠ 0) (h : Good n) :
    ∃ J : Ideal (𝓞 (CyclotomicField 5 ℚ)), absNorm J = n := by
  classical
  let Q : ℕ → Ideal (𝓞 (CyclotomicField 5 ℚ)) := fun p =>
    if hp : p.Prime then Classical.choose (exists_over p hp) else ⊤
  have hQ : ∀ p, p.Prime → absNorm (Q p) = p ^ fdeg p := fun p hp => by
    simp only [Q, dif_pos hp]; exact Classical.choose_spec (exists_over p hp)
  refine ⟨∏ p ∈ n.primeFactors, Q p ^ (n.factorization p / fdeg p), ?_⟩
  rw [map_prod]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [map_pow, hQ p hpp, ← pow_mul, Nat.mul_div_cancel' (h p hpp)]

end Eafb

open NumberField in
theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  by_cases hs : s = 0
  · exact ⟨0, by subst hs; simp⟩
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, Algebra.norm_zero] at hβ
    exact hs (pow_eq_zero_iff (by norm_num) |>.mp hβ.symm)
  have hspos : 0 ≤ s := by
    have := Eafb.norm_int_nonneg β
    rw [hβ] at this
    exact (Odd.pow_nonneg_iff (by decide)).mp this
  have hI : Ideal.absNorm (Ideal.span {β}) = s.natAbs ^ 5 := by
    rw [Ideal.absNorm_span_singleton, hβ, Int.natAbs_pow]
  have hg := Eafb.good_absNorm (Ideal.span {β}) (by simpa [Ideal.span_singleton_eq_bot] using hβ0)
  rw [hI] at hg
  obtain ⟨J, hJ⟩ := Eafb.exists_of_good s.natAbs (by simpa using hs) (Eafb.good_of_pow5 _ hg)
  obtain ⟨d, hd⟩ := (hPID.principal J).principal
  refine ⟨d, ?_⟩
  have hd' : (Algebra.norm ℤ d).natAbs = s.natAbs := by
    rw [← Ideal.absNorm_span_singleton, ← hJ, hd]
  have h1 := Eafb.norm_int_nonneg d
  have : Algebra.norm ℤ d = s := by
    rw [← Int.natAbs_of_nonneg h1, ← Int.natAbs_of_nonneg hspos, hd']
  rw [this]
