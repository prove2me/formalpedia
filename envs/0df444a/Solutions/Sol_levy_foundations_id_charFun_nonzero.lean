-- Prove2me | solution 1 for levy_foundations_id_charFun_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T08:09:48.460071+00:00
-- url     : https://prove2.me/submissions/a30ca600-1321-479b-a5e5-c24a870cbd1d

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory


private theorem nz_iter (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (LevyFoundations.iteratedConv ν n) ∧
      ∀ ξ : ℝ, charFun (LevyFoundations.iteratedConv ν n) ξ = (charFun ν ξ) ^ n := by
  induction n with
  | zero =>
    refine ⟨by simp [LevyFoundations.iteratedConv]; infer_instance, fun ξ => ?_⟩
    simp [LevyFoundations.iteratedConv]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, fun ξ => ?_⟩
    · simp only [LevyFoundations.iteratedConv]; infer_instance
    · simp only [LevyFoundations.iteratedConv]
      rw [charFun_conv, h2, pow_succ, mul_comm]

open Complex in
private theorem nz_normsq (ν : Measure ℝ) [IsProbabilityMeasure ν] (ξ : ℝ) :
    ‖charFun ν ξ‖ ^ 2 = ∫ z : ℝ × ℝ, Real.cos (ξ * (z.1 - z.2)) ∂(ν.prod ν) := by
  set f : ℝ → ℂ := fun x => cexp ((ξ : ℂ) * x * I) with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hfn : ∀ x, ‖f x‖ = 1 := fun x => by
    simp only [hf]
    have : (ξ : ℂ) * x * I = ((ξ * x : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ g : ℝ → ℂ, Continuous g → (∀ x, ‖g x‖ = 1) → Integrable g ν := by
    intro g hg hgn
    refine Integrable.of_bound (C := 1) hg.aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hgn x).le)
  have hψ : charFun ν ξ = ∫ x, f x ∂ν := by simp [charFun_apply_real, hf]
  have hconj : (starRingEnd ℂ) (charFun ν ξ) = ∫ y, (starRingEnd ℂ) (f y) ∂ν := by
    rw [hψ]; exact (integral_conj).symm
  have hprod : charFun ν ξ * (starRingEnd ℂ) (charFun ν ξ)
      = ∫ z : ℝ × ℝ, f z.1 * (starRingEnd ℂ) (f z.2) ∂(ν.prod ν) := by
    rw [hconj, hψ]
    exact (integral_prod_mul (μ := ν) (ν := ν) f (fun y => (starRingEnd ℂ) (f y))).symm
  have hmul : charFun ν ξ * (starRingEnd ℂ) (charFun ν ξ) = ((‖charFun ν ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; simp [Complex.normSq_eq_norm_sq]
  have hI : Integrable (fun z : ℝ × ℝ => f z.1 * (starRingEnd ℂ) (f z.2)) (ν.prod ν) := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ => f z.1 * (starRingEnd ℂ) (f z.2)).aestronglyMeasurable
    · simp [hfn]
  have heq : ((‖charFun ν ξ‖ ^ 2 : ℝ) : ℂ) = ∫ z : ℝ × ℝ, f z.1 * (starRingEnd ℂ) (f z.2) ∂(ν.prod ν) :=
    hmul.symm.trans hprod
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  have h2 := integral_re hI
  simp only [RCLike.re_to_complex] at h2
  rw [hre, ← h2]
  congr 1; ext z
  simp only [hf]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : (ξ : ℂ) * (z.1 : ℂ) * I + (starRingEnd ℂ) ((ξ : ℂ) * (z.2 : ℂ) * I)
      = ((ξ * (z.1 - z.2) : ℝ) : ℂ) * I := by
    simp [Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

private theorem nz_ineq (ν : Measure ℝ) [IsProbabilityMeasure ν] (ξ : ℝ) :
    1 - ‖charFun ν (2 * ξ)‖ ^ 2 ≤ 4 * (1 - ‖charFun ν ξ‖ ^ 2) := by
  rw [nz_normsq ν (2 * ξ), nz_normsq ν ξ]
  have hi : ∀ c : ℝ, Integrable (fun z : ℝ × ℝ => Real.cos (c * (z.1 - z.2))) (ν.prod ν) := by
    intro c
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ × ℝ => Real.cos (c * (z.1 - z.2))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have h1 : ∀ c : ℝ, 1 - ∫ z : ℝ × ℝ, Real.cos (c * (z.1 - z.2)) ∂(ν.prod ν)
      = ∫ z : ℝ × ℝ, (1 - Real.cos (c * (z.1 - z.2))) ∂(ν.prod ν) := by
    intro c
    rw [integral_sub (integrable_const _) (hi c)]; simp
  rw [h1, h1, ← integral_const_mul]
  refine integral_mono ((integrable_const _).sub (hi _)) ((((integrable_const _).sub (hi _))).const_mul 4) ?_
  intro z
  simp only
  have e : 2 * ξ * (z.1 - z.2) = 2 * (ξ * (z.1 - z.2)) := by ring
  rw [e, Real.cos_two_mul]
  have := Real.cos_le_one (ξ * (z.1 - z.2))
  have := Real.neg_one_le_cos (ξ * (z.1 - z.2))
  nlinarith


theorem solution {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) : ∀ ξ : ℝ, charFun μ ξ ≠ 0 := by
  intro ξ
  have hc : Continuous (charFun μ) := continuous_charFun
  have h0 : charFun μ 0 = 1 := by simp
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  have hnear : ∀ η : ℝ, |η| < δ → 1 / 4 ≤ ‖charFun μ η‖ ^ 2 := by
    intro η hη
    have h1 := hδ' (x := η) (by simpa [Real.dist_eq] using hη)
    rw [h0, dist_eq_norm, norm_sub_rev] at h1
    have h2 := norm_sub_norm_le (1 : ℂ) (charFun μ η)
    rw [norm_one] at h2
    have h3 : 1 / 2 < ‖charFun μ η‖ := by linarith
    nlinarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|ξ| / δ) (by norm_num : (1 : ℝ) < 2)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set η : ℝ := ξ / 2 ^ k with hη
  have hηδ : |η| < δ := by
    rw [hη, abs_div, abs_of_pos h2k, div_lt_iff₀ h2k]
    have := (div_lt_iff₀ hδ).1 hk
    linarith
  have hξη : (2 : ℝ) ^ k * η = ξ := by rw [hη]; field_simp
  have hiter : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (j : ℕ),
      1 - ‖charFun ν (2 ^ j * η)‖ ^ 2 ≤ 4 ^ j * (1 - ‖charFun ν η‖ ^ 2) := by
    intro ν _ j
    induction j with
    | zero => simp
    | succ j ih =>
      have := nz_ineq ν (2 ^ j * η)
      have e : (2 : ℝ) * (2 ^ j * η) = 2 ^ (j + 1) * η := by ring
      rw [e] at this
      calc 1 - ‖charFun ν (2 ^ (j + 1) * η)‖ ^ 2 ≤ 4 * (1 - ‖charFun ν (2 ^ j * η)‖ ^ 2) := this
        _ ≤ 4 * (4 ^ j * (1 - ‖charFun ν η‖ ^ 2)) := by linarith
        _ = 4 ^ (j + 1) * (1 - ‖charFun ν η‖ ^ 2) := by ring
  set n : ℕ := 2 * 4 ^ k + 1 with hn
  have hnpos : 0 < n := by omega
  obtain ⟨ν, hνp, hμν⟩ := hμ n hnpos
  have hφ : ∀ x, charFun μ x = (charFun ν x) ^ n := by
    intro x; rw [hμν]; exact (nz_iter ν n).2 x
  set a : ℝ := ‖charFun ν η‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    have := norm_charFun_le_one (μ := ν) η
    rw [ha]; nlinarith [norm_nonneg (charFun ν η)]
  have hpow : 1 / 4 ≤ a ^ n := by
    have := hnear η hηδ
    rw [hφ η, norm_pow, ← pow_mul, mul_comm, pow_mul] at this
    exact this
  have hexp : a ^ n ≤ Real.exp (-((n : ℝ) * (1 - a))) := by
    have h1 : a ≤ Real.exp (-(1 - a)) := by
      have := Real.add_one_le_exp (-(1 - a)); linarith
    calc a ^ n ≤ (Real.exp (-(1 - a))) ^ n := pow_le_pow_left₀ ha0 h1 n
      _ = Real.exp (-((n : ℝ) * (1 - a))) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
  have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hbound : (n : ℝ) * (1 - a) ≤ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : Real.exp 2 < Real.exp ((n : ℝ) * (1 - a)) := Real.exp_lt_exp.2 hcon
    have h2 : 1 / 4 ≤ Real.exp (-((n : ℝ) * (1 - a))) := hpow.trans hexp
    have h3 : Real.exp ((n : ℝ) * (1 - a)) * Real.exp (-((n : ℝ) * (1 - a))) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-((n : ℝ) * (1 - a)))
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have h1a : 1 - a ≤ 2 / n := by rw [le_div_iff₀ hnR]; linarith
  have hfin := hiter ν k
  rw [hξη] at hfin
  have hlt : (4 : ℝ) ^ k * (2 / n) < 1 := by
    rw [mul_div_assoc', div_lt_one hnR]
    have : ((n : ℕ) : ℝ) = 2 * 4 ^ k + 1 := by rw [hn]; push_cast; ring
    rw [this]; linarith [pow_pos (by norm_num : (0 : ℝ) < 4) k]
  have hpos : 0 < ‖charFun ν ξ‖ ^ 2 := by
    have h4k : (0 : ℝ) ≤ 4 ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1a h4k]
  have hne : charFun ν ξ ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [hφ ξ]; exact pow_ne_zero _ hne
