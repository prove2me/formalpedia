-- Prove2me | solution 1 for waiting_time_tail_decay
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:08:38.075249+00:00
-- url     : https://prove2.me/submissions/99c55209-2845-4c46-9e51-7b1468c5ae1d

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
open Finset Set Filter Topology
open scoped BigOperators

theorem solution (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    Filter.Tendsto (fun t => t * (1 -
      ∑ k ∈ Finset.Ico (mp+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)))
      Filter.atTop (nhds 0) := by
  -- inline `full_sum_eq_one` + `one_sub_Fcdf`: rewrite (1 - upper sum) = lower partial sum (k=0..mp)
  have hone_sub : ∀ s : ℝ,
      1 - ∑ k ∈ Finset.Ico (mp+1) (N+1),
            (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k)
        = ∑ k ∈ Finset.range (mp+1),
            (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k * (Real.exp (-(lam * s))) ^ (N - k) := by
    intro s
    set e := Real.exp (-(lam * s)) with he
    -- full binomial sum = 1
    have hfull : (∑ k ∈ Finset.range (N+1),
        (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k)) = 1 := by
      have hb : ((1 - e) + e) ^ N = ∑ k ∈ Finset.range (N+1),
          (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := add_pow (1-e) e N
      have hcongr : (∑ k ∈ Finset.range (N+1), (Nat.choose N k : ℝ) * (1 - e) ^ k * e ^ (N - k))
          = ∑ k ∈ Finset.range (N+1), (1 - e) ^ k * e ^ (N - k) * (Nat.choose N k : ℝ) := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hcongr, ← hb]
      norm_num
    have hsplit : Finset.range (N+1) = Finset.range (mp+1) ∪ Finset.Ico (mp+1) (N+1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    have hdisj : Disjoint (Finset.range (mp+1)) (Finset.Ico (mp+1) (N+1)) := by
      rw [Finset.range_eq_Ico]; apply Finset.Ico_disjoint_Ico_consecutive
    rw [hsplit, Finset.sum_union hdisj] at hfull
    linarith [hfull]
  -- rewrite the whole function via hone_sub then mul_sum
  have hrw : (fun t => t * (1 -
        ∑ k ∈ Finset.Ico (mp+1) (N+1),
          (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)))
      = (fun t => ∑ k ∈ Finset.range (mp+1),
          t * ((Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
              * (Real.exp (-(lam * t))) ^ (N - k))) := by
    funext t
    rw [hone_sub t, Finset.mul_sum]
  rw [hrw]
  -- show the sum tends to 0 = ∑ 0
  have hzero : (0 : ℝ) = ∑ k ∈ Finset.range (mp+1), (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_finset_sum (Finset.range (mp+1))
  intro k hk
  rw [Finset.mem_range] at hk
  have hkN : k < N := by omega
  -- each term → 0 by squeeze; t·e^{-λt} → 0
  have htexp : Tendsto (fun t : ℝ => t * Real.exp (-(lam * t))) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hlin : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hlam tendsto_id
    have hc := hcomp.comp hlin
    have : Tendsto (fun t : ℝ => (1/lam) * ((lam * t) ^ 1 * Real.exp (-(lam * t)))) atTop (𝓝 ((1/lam) * 0)) :=
      hc.const_mul (1/lam)
    rw [mul_zero] at this
    refine this.congr ?_
    intro t
    field_simp
  set g : ℝ → ℝ := fun t => (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k
      * (Real.exp (-(lam * t))) ^ (N - k) with hg
  apply squeeze_zero_norm' (a := fun t => (Nat.choose N k : ℝ) * (t * Real.exp (-(lam * t))))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
    have he1 : Real.exp (-(lam * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
    have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
    have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
    have hpm : (1 - Real.exp (-(lam * t))) ^ k ≤ 1 := pow_le_one₀ hq0 hq1
    have hNk : 1 ≤ N - k := by omega
    have hpe : (Real.exp (-(lam * t))) ^ (N - k) ≤ Real.exp (-(lam * t)) := by
      calc (Real.exp (-(lam * t))) ^ (N - k)
          ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNk
        _ = Real.exp (-(lam * t)) := by rw [pow_one]
    have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - k) := pow_nonneg he.le _
    rw [Real.norm_eq_abs]
    have habs : |t * g t|
        = (Nat.choose N k : ℝ) * (t * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))) := by
      rw [hg]
      rw [show t * ((Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
          = (Nat.choose N k : ℝ) * (t * ((1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))) by ring]
      rw [abs_of_nonneg (by positivity)]
    rw [habs]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ ht
    calc (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
        ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
      _ = Real.exp (-(lam * t)) := by ring
  · have := htexp.const_mul (Nat.choose N k : ℝ)
    rw [mul_zero] at this
    exact this

#print axioms solution
