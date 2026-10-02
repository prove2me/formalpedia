-- Prove2me | solution 2 for flt5_cyc5_pid_core_zz5_part
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:23:34.428962+00:00
-- url     : https://prove2.me/submissions/e2fddaf6-8d53-4545-97b5-9927fb4e2c52

import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

set_option autoImplicit false

open NumberField in
lemma cyc5zz_norm_nonneg (y : CyclotomicField 5 ℚ) : 0 ≤ Algebra.norm ℚ y := by
  have : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  by_cases hy : y = 0
  · simp [hy]
  let c : (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ) → (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ) :=
    fun σ => ((Complex.conjAe.restrictScalars ℚ).toAlgHom).comp σ
  have hc : ∀ σ, c σ y = (starRingEnd ℂ) (σ y) := fun σ => rfl
  have hne : ∀ σ : (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ), σ y ≠ 0 := fun σ => by
    simpa using (map_ne_zero σ).mpr hy
  have h1 : ∏ σ : (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ), (σ y / ((‖σ y‖ : ℝ) : ℂ)) = 1 := by
    apply Finset.prod_involution (fun σ _ => c σ)
    · intro σ _
      rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, ← Complex.ofReal_mul,
        Complex.normSq_eq_norm_sq, sq]
      have : (‖σ y‖ : ℂ) ≠ 0 := by simpa using hne σ
      field_simp
    · intro σ _ _ heq
      have hz : IsPrimitiveRoot (σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))) 5 :=
        hζ.map_of_injective σ.injective
      have hcz : (starRingEnd ℂ) (σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))) =
          σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)) := by
        change c σ _ = σ _
        rw [heq]
      set z := σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))
      have hzr : (z.re : ℂ) = z := Complex.conj_eq_iff_re.mp hcz
      have h5 : z.re ^ 5 = 1 := by
        have := hz.pow_eq_one
        rw [← hzr] at this
        exact_mod_cast this
      have hre : z.re = 1 := by
        rcases le_or_gt 0 z.re with h0 | h0
        · exact (pow_eq_one_iff_of_nonneg h0 (by norm_num)).mp h5
        · have := Odd.pow_neg (by decide : Odd 5) h0
          linarith
      apply hz.ne_one (by norm_num)
      rw [← hzr, hre]; simp
    · intro σ _; exact Finset.mem_univ _
    · intro σ _; ext x; simp [c]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq] at h1
  · rw [h1, ← Complex.ofReal_prod] at h
    rw [show (algebraMap ℚ ℂ) (Algebra.norm ℚ y) = (((Algebra.norm ℚ y : ℚ) : ℝ) : ℂ) by simp] at h
    have h2 : ((Algebra.norm ℚ y : ℚ) : ℝ) = ∏ σ : (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ), ‖σ y‖ := by
      exact_mod_cast h
    have h3 : (0:ℝ) ≤ ((Algebra.norm ℚ y : ℚ) : ℝ) := by
      rw [h2]; exact Finset.prod_nonneg fun _ _ => norm_nonneg _
    exact_mod_cast h3
  · rw [Finset.prod_ne_zero_iff]; intro σ _; simpa using hne σ

open NumberField Polynomial in
lemma cyc5zz_ideal_absNorm (n : ℕ) [NeZero n] (c : ℤ)
    (hc : ((c : ZMod n)) ^ 4 + (c : ZMod n) ^ 3 + (c : ZMod n) ^ 2 + (c : ZMod n) + 1 = 0) :
    ∃ I : Ideal (𝓞 (CyclotomicField 5 ℚ)), Ideal.absNorm I = n := by
  have : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  let pb := hζ.integralPowerBasis
  have hmin : minpoly ℤ pb.gen = cyclotomic 5 ℤ := by
    have hm := minpoly.algebraMap_eq (A := ℤ) (B := 𝓞 (CyclotomicField 5 ℚ))
      (B' := CyclotomicField 5 ℚ) (FaithfulSMul.algebraMap_injective _ _) hζ.toInteger
    rw [hζ.integralPowerBasis_gen, ← hm]
    exact (cyclotomic_eq_minpoly hζ (by norm_num)).symm
  have hy : aeval (c : ZMod n) (minpoly ℤ pb.gen) = 0 := by
    rw [hmin]
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [cyclotomic_prime]
    simp [Finset.sum_range_succ]
    linear_combination hc
  let φ := pb.lift (c : ZMod n) hy
  have hsurj : Function.Surjective φ.toRingHom := by
    intro z
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(m : 𝓞 (CyclotomicField 5 ℚ)), by simp⟩
  refine ⟨RingHom.ker φ.toRingHom, ?_⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod]

lemma cyc5zz_arith (a b s : ℤ) (h_cop : Int.gcd a b = 1) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) :
    0 < s ∧ ∃ c : ℤ, ((c : ZMod s.toNat)) ^ 4 + (c : ZMod s.toNat) ^ 3 + (c : ZMod s.toNat) ^ 2 + (c : ZMod s.toNat) + 1 = 0 := by
  have hab0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h; push_neg at h; simp [h.1, h.2] at h_cop
  have hpos : 0 < a ^ 4 + b ^ 4 := by
    rcases hab0 with h | h
    · have : 0 < a ^ 2 := by positivity
      nlinarith [sq_nonneg b, sq_nonneg (b^2)]
    · have : 0 < b ^ 2 := by positivity
      nlinarith [sq_nonneg a, sq_nonneg (a^2)]
  have hΦpos : 0 < a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
    nlinarith [sq_nonneg (a^2 - a*b), sq_nonneg (b^2 - a*b)]
  have hs : 0 < s := by
    by_contra h; push_neg at h
    have := Odd.pow_nonpos (by decide : Odd 5) h
    linarith
  refine ⟨hs, ?_⟩
  have hab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr h_cop
  have h1 : IsCoprime b (a ^ 4) := hab.symm.pow_right
  have h2 : IsCoprime b (5 * s ^ 5) := by
    rw [← hPhi]
    have : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 =
        a ^ 4 + b * (-a ^ 3 + a ^ 2 * b - a * b ^ 2 + b ^ 3) := by ring
    rw [this]; exact h1.add_mul_left_right _
  have h3 : IsCoprime b s := (IsCoprime.pow_right_iff (by norm_num : 0 < 5)).mp h2.of_mul_right_right
  obtain ⟨u, v, huv⟩ := h3
  have hs0 : ((s : ℤ) : ZMod s.toNat) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.toNat_of_nonneg hs.le]
  have huv' : (u : ZMod s.toNat) * b = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod s.toNat)) huv
    push_cast at this; rw [hs0] at this; simpa using this
  have hΦ' : (a : ZMod s.toNat) ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 0 := by
    have := congrArg (fun x : ℤ => (x : ZMod s.toNat)) hPhi
    push_cast at this; rw [hs0] at this; simpa using this
  refine ⟨-a * u, ?_⟩
  push_cast
  set w : ZMod s.toNat := (u : ZMod s.toNat) * b
  linear_combination (u : ZMod s.toNat) ^ 4 * hΦ' -
    (((-(a : ZMod s.toNat)) * u) ^ 3 + ((-(a : ZMod s.toNat)) * u) ^ 2 * (1 + w)
      + ((-(a : ZMod s.toNat)) * u) * (1 + w + w ^ 2) + (1 + w + w ^ 2 + w ^ 3)) * huv'

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  obtain ⟨hs, c, hc⟩ := cyc5zz_arith a b s h_cop hPhi
  have hn : NeZero s.toNat := ⟨by omega⟩
  obtain ⟨I, hI⟩ := cyc5zz_ideal_absNorm s.toNat c hc
  obtain ⟨d, hd⟩ := (hPID.principal I).principal
  refine ⟨d, ?_⟩
  have h1 : (Algebra.norm ℤ d).natAbs = s.toNat := by
    rw [← Ideal.absNorm_span_singleton, ← hI, hd]
  have h2 : 0 ≤ Algebra.norm ℤ d := by
    have := cyc5zz_norm_nonneg (d : CyclotomicField 5 ℚ)
    rw [← Algebra.coe_norm_int] at this
    exact_mod_cast this
  have h3 : Algebra.norm ℤ d = s := by omega
  rw [h3]
