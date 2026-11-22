-- Prove2me | solution 1 for sum_choose_le_exp_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:05.392203+00:00
-- url     : https://prove2.me/submissions/336cd07b-e2ce-480f-82d6-571de96c8474

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by
  have hd_pos : (0 : ℝ) < ↑d := Nat.cast_pos.mpr hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hdm_r : (d : ℝ) ≤ ↑m := Nat.cast_le.mpr hdm
  have hd_div_m_pos : (0 : ℝ) < ↑d / ↑m := div_pos hd_pos hm_pos
  have hd_div_m_le : (d : ℝ) / ↑m ≤ 1 := by
    rw [div_le_one hm_pos]; exact hdm_r
  have hm_div_d_ge : (1 : ℝ) ≤ ↑m / ↑d := le_div_iff₀ hd_pos |>.mpr (by linarith)
  -- Strategy: ∑_{i=0}^d C(m,i) ≤ (m/d)^d · (1 + d/m)^m ≤ (m/d)^d · e^d = (em/d)^d
  -- Step 1: ∑_{i=0}^d C(m,i) ≤ (m/d)^d · ∑_{i=0}^d C(m,i) · (d/m)^i
  -- Because C(m,i) = C(m,i) · (d/m)^i · (m/d)^i ≤ C(m,i) · (d/m)^i · (m/d)^d
  -- (since m/d ≥ 1 and i ≤ d implies (m/d)^i ≤ (m/d)^d)
  -- Step 2: ∑_{i=0}^d C(m,i) · (d/m)^i ≤ (1 + d/m)^m
  -- Step 3: (1 + d/m)^m ≤ e^d
  -- Step 4: combine
  set t := (d : ℝ) / ↑m with ht_def
  have ht_pos : 0 < t := hd_div_m_pos
  have ht_le : t ≤ 1 := hd_div_m_le
  -- Step 2: ∑_{i=0}^d C(m,i) · t^i ≤ (1 + t)^m
  -- From binomial theorem: (1 + t)^m = ∑_{i=0}^m C(m,i) · t^i · 1^{m-i} = ∑_{i=0}^m C(m,i) · t^i
  have h_binom : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      t ^ i * (1 : ℝ) ^ (m - i) * ↑(Nat.choose m i) := by
    rw [add_comm]; exact add_pow t 1 m
  have h_binom' : (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1),
      ↑(Nat.choose m i) * t ^ i := by
    rw [h_binom]
    congr 1; ext i
    rw [one_pow, mul_one]; ring
  have h_partial_le_binom : ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i ≤
      (1 + t) ^ m := by
    rw [h_binom']
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp_all
    · intro i _ _
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
  -- Step 3: (1 + t)^m ≤ e^d
  -- (1 + t) ≤ exp(t) by add_one_le_exp
  -- So (1 + t)^m ≤ exp(t)^m = exp(t · m) = exp(d)
  have h_exp_bound : (1 + t) ^ m ≤ Real.exp 1 ^ d := by
    have h1t_le : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have h_pow : (1 + t) ^ m ≤ (Real.exp t) ^ m :=
      pow_le_pow_left₀ (by linarith) h1t_le m
    have h_exp_eq : (Real.exp t) ^ m = Real.exp (t * ↑m) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simp_all
  -- Step 1: ∑_{i=0}^d C(m,i) ≤ (m/d)^d · ∑_{i=0}^d C(m,i) · t^i
  -- For each i ≤ d: C(m,i) = C(m,i) · t^i · (1/t)^i
  -- And (1/t)^i = (m/d)^i ≤ (m/d)^d since m/d ≥ 1 and i ≤ d
  have h_factor : (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ)) ≤
      (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
    -- Rewrite LHS: C(m,i) = C(m,i) · t^i · (m/d)^i
    have h_id : ∀ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ) =
        ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i := by
      intro i _
      have htinv : t * (↑m / ↑d) = 1 := by
        simp only [ht_def]; field_simp
      rw [mul_assoc, ← mul_pow, htinv, one_pow, mul_one]
    rw [Finset.sum_congr rfl h_id]
    -- Now: ∑ C(m,i) · t^i · (m/d)^i ≤ (m/d)^d · ∑ C(m,i) · t^i
    -- because (m/d)^i ≤ (m/d)^d for i ≤ d and m/d ≥ 1
    calc ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ i
        ≤ ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i * (↑m / ↑d) ^ d := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_le : i ≤ d := by simp only [Finset.mem_range] at hi; omega
          apply mul_le_mul_of_nonneg_left
          · exact pow_right_mono₀ hm_div_d_ge hi_le
          · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt ht_pos) _)
      _ = (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := by
          rw [← Finset.sum_mul, mul_comm]
  -- Combine: ∑ C(m,i) ≤ (m/d)^d · e^d = (em/d)^d
  calc (∑ i ∈ Finset.range (d + 1), (Nat.choose m i : ℝ))
      ≤ (↑m / ↑d) ^ d * ∑ i ∈ Finset.range (d + 1), ↑(Nat.choose m i) * t ^ i := h_factor
    _ ≤ (↑m / ↑d) ^ d * ((1 + t) ^ m) := by
        apply mul_le_mul_of_nonneg_left h_partial_le_binom
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ ≤ (↑m / ↑d) ^ d * Real.exp 1 ^ d := by
        apply mul_le_mul_of_nonneg_left h_exp_bound
        exact pow_nonneg (div_nonneg (le_of_lt hm_pos) (le_of_lt hd_pos)) d
    _ = (Real.exp 1 * ↑m / ↑d) ^ d := by
        rw [mul_div_assoc, ← mul_pow, mul_comm (Real.exp 1) _]
