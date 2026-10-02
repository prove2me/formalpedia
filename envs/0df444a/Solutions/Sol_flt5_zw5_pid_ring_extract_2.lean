-- Prove2me | solution 2 for flt5_zw5_pid_ring_extract
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:50:01.969988+00:00
-- url     : https://prove2.me/submissions/0afcc746-5def-41ba-84d0-a4a7be7c265f

import Mathlib
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
theorem P2M88_norm_nonneg (y : CyclotomicField 5 ℚ) : 0 ≤ Algebra.norm ℚ y := by
  classical
  have : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
  have hζ := IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  by_cases hy : y = 0
  · simp [hy]
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  let c : (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ) → (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ) :=
    fun σ => ((starRingEnd ℂ).comp σ.toRingHom).toRatAlgHom
  have hc : ∀ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, ∀ z, c σ z = starRingEnd ℂ (σ z) :=
    fun σ z => rfl
  have hne : ∀ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ y ≠ 0 := fun σ => by
    intro h0
    exact hy ((map_eq_zero_iff σ σ.toRingHom.injective).mp h0)
  have hn0 : ∀ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, ((‖σ y‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast (norm_ne_zero_iff.mpr (hne σ))
  let f : (CyclotomicField 5 ℚ →ₐ[ℚ] ℂ) → ℂ := fun σ => σ y / ((‖σ y‖ : ℝ) : ℂ)
  have hf : ∏ σ, f σ = 1 := by
    refine Finset.prod_involution (fun σ _ => c σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
    · intro σ _
      simp only [f, hc]
      have h1 : (σ y) * starRingEnd ℂ (σ y) = ((‖σ y‖ : ℝ) : ℂ) ^ 2 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [Complex.norm_conj, div_mul_div_comm, h1, ← sq, div_self (pow_ne_zero 2 (hn0 σ))]
    · intro σ _ _ hσ
      have hz : starRingEnd ℂ (σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))) =
          σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)) := by
        have := congrArg (fun τ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ =>
          τ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))) hσ
        simpa [hc] using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hz
      have h5 : (σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ))) ^ 5 = 1 := by
        rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [hr] at h5
      have hr5 : r ^ 5 = 1 := by exact_mod_cast h5
      have hr1 : r = 1 := by
        rcases le_or_gt r 0 with h' | h'
        · have : r ^ 5 ≤ 0 := Odd.pow_nonpos (by decide) h'
          linarith
        · exact (pow_eq_one_iff_of_nonneg h'.le (by norm_num)).mp hr5
      have : σ (IsCyclotomicExtension.zeta 5 ℚ (CyclotomicField 5 ℚ)) = σ 1 := by
        rw [hr, hr1, map_one]; simp
      exact hζ.ne_one (by norm_num) (σ.toRingHom.injective this)
    · intro σ _
      ext z
      simp [hc]
  have hprod : ∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ y
      = ((∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, ‖σ y‖ : ℝ) : ℂ) := by
    have : ∀ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, σ y = ((‖σ y‖ : ℝ) : ℂ) * f σ := fun σ => by
      simp only [f]; rw [mul_div_cancel₀ _ (hn0 σ)]
    rw [Finset.prod_congr rfl (fun σ _ => this σ), Finset.prod_mul_distrib, hf, mul_one]
    push_cast; rfl
  rw [hprod] at h
  have h3 : ((Algebra.norm ℚ y : ℝ) : ℂ) = ((∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, ‖σ y‖ : ℝ) : ℂ) := by
    rw [← h]; simp
  have h4 : (Algebra.norm ℚ y : ℝ) = ∏ σ : CyclotomicField 5 ℚ →ₐ[ℚ] ℂ, ‖σ y‖ := by
    exact_mod_cast h3
  have h5 : (0:ℝ) ≤ Algebra.norm ℚ y := by
    rw [h4]; exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  exact_mod_cast h5


theorem P2M88_absNorm {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {z : K} (hζ : IsPrimitiveRoot z 5)
    (s x : ℤ) (hs : 0 < s) (hdiv : s ∣ x ^ 4 + x ^ 3 + x ^ 2 + x + 1) :
    Ideal.absNorm (Ideal.span {((s : ℤ) : NumberField.RingOfIntegers K),
      hζ.toInteger - (x : NumberField.RingOfIntegers K)}) = s.toNat := by
  classical
  set O := NumberField.RingOfIntegers K
  set I : Ideal O := Ideal.span {((s : ℤ) : O), hζ.toInteger - (x : O)} with hI
  set N : ℕ := s.toNat with hN
  have hNs : (N : ℤ) = s := Int.toNat_of_nonneg hs.le
  have hNpos : 0 < N := by omega
  have : NeZero N := ⟨hNpos.ne'⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsI : ((s : ℤ) : O) ∈ I := Ideal.subset_span (by simp)
  have hzI : hζ.toInteger - (x : O) ∈ I := Ideal.subset_span (by simp)
  -- every element is an integer mod I
  have hred : ∀ y : O, ∃ n : ℤ, y - (n : O) ∈ I := by
    intro y
    obtain ⟨f, rfl⟩ := (hζ.integralPowerBasis).exists_eq_aeval' y
    rw [IsPrimitiveRoot.integralPowerBasis_gen]
    refine ⟨f.eval x, ?_⟩
    have hd := Polynomial.sub_dvd_eval_sub hζ.toInteger (x : O) (f.map (Int.castRingHom O))
    have e1 : Polynomial.aeval hζ.toInteger f = (f.map (Int.castRingHom O)).eval hζ.toInteger := by
      rw [Polynomial.aeval_def, Polynomial.eval_map]; rfl
    have e2 : ((f.eval x : ℤ) : O) = (f.map (Int.castRingHom O)).eval (x : O) := by
      rw [Polynomial.eval_intCast_map]; simp
    rw [e1, e2]
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact I.mul_mem_right c hzI
  -- the root condition
  have hmin : minpoly ℤ hζ.integralPowerBasis.gen = Polynomial.cyclotomic 5 ℤ := by
    rw [IsPrimitiveRoot.integralPowerBasis_gen, ← NumberField.RingOfIntegers.minpoly_coe]
    change minpoly ℤ z = _
    exact (Polynomial.cyclotomic_eq_minpoly hζ (by norm_num)).symm
  have hroot : Polynomial.aeval ((x : ZMod N)) (minpoly ℤ hζ.integralPowerBasis.gen) = 0 := by
    rw [hmin, Polynomial.cyclotomic_prime ℤ 5]
    have h0 : (((x ^ 4 + x ^ 3 + x ^ 2 + x + 1 : ℤ)) : ZMod N) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hNs]; exact hdiv
    push_cast at h0
    simp [Finset.sum_range_succ]
    linear_combination h0
  let φ : O →+* ZMod N := (hζ.integralPowerBasis.lift ((x : ZMod N)) hroot).toRingHom
  have hφζ : φ hζ.toInteger = (x : ZMod N) := by
    have := hζ.integralPowerBasis.lift_gen ((x : ZMod N)) hroot
    rw [IsPrimitiveRoot.integralPowerBasis_gen] at this
    exact this
  have hle : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, hNs]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hφζ, map_intCast, sub_self]
  have hker : I = RingHom.ker φ := by
    refine le_antisymm hle ?_
    intro y hy
    obtain ⟨n, hn⟩ := hred y
    have h1 : φ (y - (n : O)) = 0 := hle hn
    rw [RingHom.mem_ker] at hy
    rw [map_sub, hy, map_intCast, zero_sub, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd,
      hNs] at h1
    obtain ⟨k, hk⟩ := h1
    have hnI : (n : O) ∈ I := by
      rw [hk, Int.cast_mul]; exact I.mul_mem_right _ hsI
    have := I.add_mem hn hnI
    simpa using this
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨((z.val : ℕ) : O), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hker,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod]

set_option backward.isDefEq.respectTransparency false in
theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1) (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) (h5sum : (5 : ℤ) ∣ a + b) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  classical
  have : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
  have hζ := IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)
  have hΦnn : 0 ≤ a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b)),
      mul_nonneg (sq_nonneg (a - b)) (sq_nonneg a), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg b),
      sq_nonneg (a * b)]
  have hs0 : 0 ≤ s := by
    by_contra h
    have h' : s < 0 := lt_of_not_ge h
    have : s ^ 5 < 0 := Odd.pow_neg (by decide) h'
    linarith
  rcases hs0.eq_or_lt with hs | hs
  · refine ⟨0, ?_⟩
    rw [← hs, Algebra.norm_zero]
  have hcopab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr h_cop
  have hbs : IsCoprime b s := by
    have h1 : IsCoprime b (a ^ 4) := hcopab.symm.pow_right
    have h2 : IsCoprime b (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
      have e : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4
          = a ^ 4 + b * (-a ^ 3 + a ^ 2 * b - a * b ^ 2 + b ^ 3) := by ring
      rw [e]; exact h1.add_mul_left_right _
    rw [hPhi] at h2
    have h3 : IsCoprime b (s ^ 5) := h2.of_mul_right_right
    exact (IsCoprime.pow_right_iff (by norm_num)).mp h3
  obtain ⟨u, v, huv⟩ := hbs
  have hdiv : s ∣ (-a * u) ^ 4 + (-a * u) ^ 3 + (-a * u) ^ 2 + (-a * u) + 1 := by
    refine ⟨5 * u ^ 4 * s ^ 4 + v * (-a ^ 3 * u ^ 3 + a ^ 2 * u ^ 2 * (1 + b * u)
      - a * u * (1 + b * u + b ^ 2 * u ^ 2) + (1 + b * u + b ^ 2 * u ^ 2 + b ^ 3 * u ^ 3)), ?_⟩
    linear_combination u ^ 4 * hPhi - (-a ^ 3 * u ^ 3 + a ^ 2 * u ^ 2 * (1 + b * u)
      - a * u * (1 + b * u + b ^ 2 * u ^ 2) + (1 + b * u + b ^ 2 * u ^ 2 + b ^ 3 * u ^ 3)) * huv
  have hN := P2M88_absNorm hζ s (-a * u) hs hdiv
  obtain ⟨d, hd⟩ := (hPID.principal (Ideal.span {((s : ℤ) : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)),
      hζ.toInteger - ((-a * u : ℤ) : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))})).principal
  rw [hd] at hN
  change Ideal.absNorm (Ideal.span {d}) = _ at hN
  rw [Ideal.absNorm_span_singleton] at hN
  have hnn : 0 ≤ Algebra.norm ℤ d := by
    have h0 := P2M88_norm_nonneg (d : CyclotomicField 5 ℚ)
    rw [← Algebra.coe_norm_int] at h0
    exact_mod_cast h0
  refine ⟨d, ?_⟩
  have h1 : ((Algebra.norm ℤ d).natAbs : ℤ) = (s.toNat : ℤ) := by rw [hN]
  rw [Int.natAbs_of_nonneg hnn, Int.toNat_of_nonneg hs.le] at h1
  rw [h1]
