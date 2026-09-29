-- Prove2me | solution 1 for waiting_time_t_density_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T22:08:37.763682+00:00
-- url     : https://prove2.me/submissions/19c616cf-30dd-4e74-ab18-f086ac49cdfd

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem solution (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn (fun t =>
      t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)) (Set.Ioi (0:ℝ)) := by
  -- dominating constant
  set D : ℝ := |(N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam| with hD
  -- dominating function:  (D * 2 / lam) * exp (-(lam/2) * t)
  set C : ℝ := D * 2 / lam with hC
  have hgint : IntegrableOn (fun t : ℝ => C * Real.exp (-(lam/2) * t)) (Ioi (0:ℝ)) := by
    have := integrableOn_exp_mul_Ioi (a := -(lam/2)) (c := (0:ℝ)) (by linarith)
    exact this.const_mul C
  have hcont : Continuous (fun t : ℝ => t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ)
      * (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp) * lam)) := by
    fun_prop
  refine Integrable.mono' hgint hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Set.mem_Ioi] at ht
  have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
  have he1 : Real.exp (-(lam * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [ht, hlam]
  have hq0 : (0:ℝ) ≤ 1 - Real.exp (-(lam * t)) := by linarith
  have hq1 : 1 - Real.exp (-(lam * t)) ≤ 1 := by linarith [he.le]
  have hpm : (1 - Real.exp (-(lam * t))) ^ mp ≤ 1 := pow_le_one₀ hq0 hq1
  have hpm0 : (0:ℝ) ≤ (1 - Real.exp (-(lam * t))) ^ mp := pow_nonneg hq0 _
  have hNmp : 1 ≤ N - mp := by omega
  -- (e^{-λt})^{N-mp} ≤ e^{-λt}
  have hpe : (Real.exp (-(lam * t))) ^ (N - mp) ≤ Real.exp (-(lam * t)) := by
    calc (Real.exp (-(lam * t))) ^ (N - mp)
        ≤ (Real.exp (-(lam * t))) ^ 1 := pow_le_pow_of_le_one he.le he1 hNmp
      _ = Real.exp (-(lam * t)) := by rw [pow_one]
  have hpe0 : (0:ℝ) ≤ (Real.exp (-(lam * t))) ^ (N - mp) := pow_nonneg he.le _
  -- key analytic bound: t · e^{-λt} ≤ (2/λ) · e^{-(λ/2)t}
  have hkey : t * Real.exp (-(lam * t)) ≤ (2 / lam) * Real.exp (-(lam/2) * t) := by
    have hx : (lam/2) * t ≤ Real.exp ((lam/2) * t) := by
      have := Real.add_one_le_exp ((lam/2) * t)
      linarith
    have hpos : (0:ℝ) < Real.exp (-(lam/2) * t) := Real.exp_pos _
    have hmul : (lam/2) * t * Real.exp (-(lam/2) * t) ≤ 1 := by
      have h2 : (lam/2) * t * Real.exp (-(lam/2) * t)
          ≤ Real.exp ((lam/2) * t) * Real.exp (-(lam/2) * t) := by
        apply mul_le_mul_of_nonneg_right hx hpos.le
      rw [← Real.exp_add] at h2
      have : (lam/2) * t + -(lam/2) * t = 0 := by ring
      rw [this, Real.exp_zero] at h2
      exact h2
    have ht2 : t * Real.exp (-(lam/2) * t) ≤ 2 / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [hmul]
    have hsplit : Real.exp (-(lam * t)) = Real.exp (-(lam/2) * t) * Real.exp (-(lam/2) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc t * Real.exp (-(lam * t))
        = (t * Real.exp (-(lam/2) * t)) * Real.exp (-(lam/2) * t) := by rw [hsplit]; ring
      _ ≤ (2 / lam) * Real.exp (-(lam/2) * t) := by
          apply mul_le_mul_of_nonneg_right ht2 hpos.le
  -- assemble
  rw [Real.norm_eq_abs]
  have ht0 : (0:ℝ) ≤ t := ht.le
  have habs : |t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)|
      = D * (t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))) := by
    rw [hD]
    rw [show t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)
        = ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * lam)
            * (t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))) by ring]
    rw [abs_mul, abs_of_nonneg (a := t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))) (by positivity)]
  rw [habs]
  have hDnn : (0:ℝ) ≤ D := by rw [hD]; exact abs_nonneg _
  have hbound1 : t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp))
      ≤ t * Real.exp (-(lam * t)) := by
    apply mul_le_mul_of_nonneg_left _ ht0
    calc (1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)
        ≤ 1 * Real.exp (-(lam * t)) := mul_le_mul hpm hpe hpe0 (by norm_num)
      _ = Real.exp (-(lam * t)) := by ring
  calc D * (t * ((1 - Real.exp (-(lam * t))) ^ mp * (Real.exp (-(lam * t))) ^ (N - mp)))
      ≤ D * (t * Real.exp (-(lam * t))) := by
        apply mul_le_mul_of_nonneg_left hbound1 hDnn
    _ ≤ D * ((2 / lam) * Real.exp (-(lam/2) * t)) := by
        apply mul_le_mul_of_nonneg_left hkey hDnn
    _ = C * Real.exp (-(lam/2) * t) := by rw [hC]; ring

#print axioms solution
