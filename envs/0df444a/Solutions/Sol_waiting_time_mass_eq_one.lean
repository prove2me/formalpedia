-- Prove2me | solution 1 for waiting_time_mass_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:21:53.510189+00:00
-- url     : https://prove2.me/submissions/b7f20f05-65d1-4236-b164-a4583ef87827

import Theorems.Thm_Waiting_waiting_time_density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Filter.AtTopBot.Field

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory Set Filter Topology

private noncomputable def Fc (N m : ℕ) (lam : ℝ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico (m+1) (N+1),
    (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
      * (Real.exp (-(lam * s))) ^ (N - k)
private noncomputable def fd (N m : ℕ) (lam : ℝ) (s : ℝ) : ℝ :=
  (N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
      * (Real.exp (-(lam * s))) ^ (N - m) * lam

private theorem Fc_zero (N m : ℕ) (lam : ℝ) (h : m < N) : Fc N m lam 0 = 0 := by
  unfold Fc
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  have : (0:ℝ) ^ k = 0 := by apply zero_pow; omega
  rw [this]; ring

private theorem Fc_tendsto (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    Tendsto (Fc N m lam) atTop (𝓝 1) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp (-(lam * s))) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => -(lam * s)) atTop atBot := by
      have h1 : Tendsto (fun s : ℝ => lam * s) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hlam tendsto_id
      exact tendsto_neg_atTop_atBot.comp h1
    exact Real.tendsto_exp_atBot.comp this
  have hq : Tendsto (fun s : ℝ => 1 - Real.exp (-(lam * s))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hexp
  have hterm : ∀ k ∈ Finset.Ico (m+1) (N+1),
      Tendsto (fun s : ℝ => (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
        * (Real.exp (-(lam * s))) ^ (N - k)) atTop (𝓝 (if k = N then 1 else 0)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    by_cases hkN : k = N
    · subst hkN
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul]
      have := hq.pow k
      simpa using this
    · rw [if_neg hkN]
      have h0 : Tendsto (fun s : ℝ => (Real.exp (-(lam * s))) ^ (N - k)) atTop (𝓝 0) := by
        have := hexp.pow (N-k)
        simpa [zero_pow (Nat.sub_ne_zero_of_lt (by omega : k < N))] using this
      have hqk : Tendsto (fun s : ℝ => (1 - Real.exp (-(lam * s))) ^ k) atTop (𝓝 1) := by
        simpa using hq.pow k
      have : Tendsto (fun s : ℝ => (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * s))) ^ k
          * (Real.exp (-(lam * s))) ^ (N - k)) atTop (𝓝 ((Nat.choose N k : ℝ) * 1 * 0)) :=
        ((tendsto_const_nhds.mul hqk).mul h0)
      simpa using this
  have hsum := tendsto_finset_sum (Finset.Ico (m+1) (N+1)) hterm
  unfold Fc
  have hval : (∑ k ∈ Finset.Ico (m+1) (N+1), (if k = N then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.Ico (m+1) (N+1)) N (fun _ => (1:ℝ))]
    rw [if_pos]; rw [Finset.mem_Ico]; omega
  rw [hval] at hsum
  exact hsum

private theorem fd_integrable (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    IntegrableOn (fd N m lam) (Ioi (0:ℝ)) := by
  set C : ℝ := |(N : ℝ) * (Nat.choose (N-1) m : ℝ) * lam| with hC
  have hgint : IntegrableOn (fun s : ℝ => C * Real.exp (-lam * s)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -lam) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fd N m lam) := by unfold fd; fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Set.mem_Ioi] at hs
  have he : (0:ℝ) < Real.exp (-(lam * s)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * s)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [hs, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * s)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * s)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * s))) ^ m ≤ 1 := pow_le_one₀ hq0 hq1
  have hNm : 1 ≤ N - m := by omega
  have hpe : (Real.exp (-(lam * s))) ^ (N - m) ≤ Real.exp (-(lam * s)) := by
    calc (Real.exp (-(lam * s))) ^ (N - m)
        ≤ (Real.exp (-(lam * s))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNm
      _ = Real.exp (-(lam * s)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * s))) ^ (N - m) := pow_nonneg he.le _
  unfold fd
  rw [Real.norm_eq_abs]
  have hrw : |(N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
      * (Real.exp (-(lam * s))) ^ (N - m) * lam|
      = C * ((1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)) := by
    rw [hC]
    rw [show (N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
      * (Real.exp (-(lam * s))) ^ (N - m) * lam
      = ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * lam)
        * ((1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)) by ring]
    rw [abs_mul, abs_of_nonneg (a := (1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)) (by positivity)]
  rw [hrw]
  rw [show C * Real.exp (-lam * s) = C * Real.exp (-(lam * s)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by rw [hC]; exact abs_nonneg _)
  calc (1 - Real.exp (-(lam * s))) ^ m * (Real.exp (-(lam * s))) ^ (N - m)
      ≤ 1 * Real.exp (-(lam * s)) := mul_le_mul hpm hpe hpe0 (by norm_num)
    _ = Real.exp (-(lam * s)) := by ring

theorem solution (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    ∫ s in Set.Ioi (0:ℝ),
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
        * (Real.exp (-(lam * s))) ^ (N - m) * lam) = 1 := by
  have hdens : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (Fc N m lam) (fd N m lam x) x := by
    intro x _
    have := Waiting.waiting_time_density N m lam h x
    exact this
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0:ℝ)) (f := Fc N m lam) (f' := fd N m lam) (m := (1:ℝ))
    ((Waiting.waiting_time_density N m lam h 0).continuousAt.continuousWithinAt)
    hdens (fd_integrable N m lam h hlam) (Fc_tendsto N m lam h hlam)
  have hgoal : (∫ s in Set.Ioi (0:ℝ),
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
        * (Real.exp (-(lam * s))) ^ (N - m) * lam))
      = ∫ s in Ioi (0:ℝ), fd N m lam s := by rfl
  rw [hgoal, key, Fc_zero N m lam h]; ring
