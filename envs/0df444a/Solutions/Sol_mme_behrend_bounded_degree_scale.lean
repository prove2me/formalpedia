-- Prove2me | solution 1 for mme_behrend_bounded_degree_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:17:37.848406+00:00
-- url     : https://prove2.me/submissions/94beea30-2877-449e-bd27-720dca01da68

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

private theorem behrend_scale_real
    (r d q : ℝ) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (hdexp : d ≤ Real.exp (4 * r ^ 2))
    (hqlo : d * Real.exp (1000 * r) ≤ q)
    (hqhi : q ≤ 2 * d * Real.exp (1000 * r)) :
    6 * d ≤ q * Real.exp (-4 * Real.sqrt (Real.log q)) ∧
      4 * q ≤ d * Real.exp (2000 * r) := by
  have hd0 : 0 ≤ d := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le (mul_pos (by linarith) (Real.exp_pos _)) hqlo
  have htwo : (2 : ℝ) ≤ Real.exp (r ^ 2) := by
    calc
      (2 : ℝ) ≤ 1 + r ^ 2 := by nlinarith
      _ ≤ Real.exp (r ^ 2) := by
        simpa [add_comm] using Real.add_one_le_exp (r ^ 2)
  have h1000 : Real.exp (1000 * r) ≤ Real.exp (1000 * r ^ 2) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hscale :
      2 * d * Real.exp (1000 * r) ≤ Real.exp (1024 * r ^ 2) := by
    calc
      2 * d * Real.exp (1000 * r) ≤
          Real.exp (r ^ 2) * Real.exp (4 * r ^ 2) *
            Real.exp (1000 * r ^ 2) := by gcongr
      _ = Real.exp (1005 * r ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (1024 * r ^ 2) := by
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg r])
  have hlog : Real.log q ≤ 1024 * r ^ 2 := by
    rw [Real.log_le_iff_le_exp hq0]
    exact hqhi.trans hscale
  have hsqrt : Real.sqrt (Real.log q) ≤ 32 * r := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        Real.log q ≤ 1024 * r ^ 2 := hlog
        _ = (32 * r) ^ 2 := by ring
  have hneg :
      Real.exp (-128 * r) ≤
        Real.exp (-4 * Real.sqrt (Real.log q)) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hlower :
      d * Real.exp (872 * r) ≤
        q * Real.exp (-4 * Real.sqrt (Real.log q)) := by
    calc
      d * Real.exp (872 * r) =
          (d * Real.exp (1000 * r)) * Real.exp (-128 * r) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ q * Real.exp (-4 * Real.sqrt (Real.log q)) := by
        exact mul_le_mul hqlo hneg (Real.exp_pos _).le hq0.le
  have hsix : (6 : ℝ) ≤ Real.exp (872 * r) := by
    calc
      (6 : ℝ) ≤ 1 + 872 * r := by nlinarith
      _ ≤ Real.exp (872 * r) := by
        simpa [add_comm] using Real.add_one_le_exp (872 * r)
  have heighteen : (8 : ℝ) ≤ Real.exp (1000 * r) := by
    calc
      (8 : ℝ) ≤ 1 + 1000 * r := by nlinarith
      _ ≤ Real.exp (1000 * r) := by
        simpa [add_comm] using Real.add_one_le_exp (1000 * r)
  constructor
  · have h := mul_le_mul_of_nonneg_left hsix hd0
    simpa [mul_comm] using h.trans hlower
  · calc
      4 * q ≤ 8 * d * Real.exp (1000 * r) := by nlinarith
      _ ≤ d * Real.exp (1000 * r) * Real.exp (1000 * r) := by
        nlinarith [mul_le_mul_of_nonneg_right heighteen hd0]
      _ = d * Real.exp (2000 * r) := by
        rw [mul_assoc, ← Real.exp_add]
        ring

private theorem nat_le_five_pow_exp_bound
    (N D : ℕ) (hD : D ≤ 5 ^ N) :
    (D : ℝ) ≤
      Real.exp (4 * Real.sqrt (((N + 1 : ℕ) : ℝ)) ^ 2) := by
  have hcast : (D : ℝ) ≤ (5 : ℝ) ^ N := by
    exact_mod_cast hD
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by
    calc
      (5 : ℝ) = 4 + 1 := by norm_num
      _ ≤ Real.exp 4 := Real.add_one_le_exp 4
  have hpow : (5 : ℝ) ^ N ≤ (Real.exp 4) ^ N :=
    pow_le_pow_left₀ (by norm_num) hfive N
  have hexp : (Real.exp 4) ^ N = Real.exp (4 * (N : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsqrt : Real.sqrt (((N + 1 : ℕ) : ℝ)) ^ 2 = (N + 1 : ℕ) := by
    exact Real.sq_sqrt (by positivity)
  calc
    (D : ℝ) ≤ (5 : ℝ) ^ N := hcast
    _ ≤ (Real.exp 4) ^ N := hpow
    _ = Real.exp (4 * (N : ℝ)) := hexp
    _ ≤ Real.exp (4 * Real.sqrt (((N + 1 : ℕ) : ℝ)) ^ 2) := by
      rw [Real.exp_le_exp]
      rw [hsqrt]
      push_cast
      nlinarith

theorem solution
    (N D : ℕ) (hD1 : 1 ≤ D) (hD5 : D ≤ 5 ^ N) :
    let r := Real.sqrt (((N + 1 : ℕ) : ℝ))
    let Q := Nat.ceil ((D : ℝ) * Real.exp (1000 * r))
    0 < Q ∧
      (6 * D : ℝ) ≤
        (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ∧
      (4 * Q : ℝ) ≤ (D : ℝ) * Real.exp (2000 * r) := by
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let x : ℝ := (D : ℝ) * Real.exp (1000 * r)
  let Q : ℕ := Nat.ceil x
  have hr : 1 ≤ r := by
    change 1 ≤ Real.sqrt (((N + 1 : ℕ) : ℝ))
    rw [Real.one_le_sqrt]
    norm_num
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hx0 : 0 ≤ x := by positivity
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he : (1 : ℝ) ≤ Real.exp (1000 * r) :=
      Real.one_le_exp (by positivity)
    nlinarith [mul_le_mul hd he (by norm_num) (by positivity)]
  have hxQ : x ≤ (Q : ℝ) := by
    simpa only [Q] using Nat.le_ceil x
  have hQx : (Q : ℝ) ≤ 2 * x := by
    have hlt : (Q : ℝ) < x + 1 := by
      simpa only [Q] using Nat.ceil_lt_add_one hx0
    linarith
  have hQpos : 0 < Q := by
    change 0 < Nat.ceil x
    rw [Nat.ceil_pos]
    exact lt_of_lt_of_le zero_lt_one hx1
  have hdexp : (D : ℝ) ≤ Real.exp (4 * r ^ 2) := by
    simpa only [r] using nat_le_five_pow_exp_bound N D hD5
  have hreal := behrend_scale_real r (D : ℝ) (Q : ℝ) hr hd hdexp
    (by simpa only [x] using hxQ)
    (by simpa only [x, mul_assoc] using hQx)
  change 0 < Q ∧
    (6 * D : ℝ) ≤
      (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ∧
    (4 * Q : ℝ) ≤ (D : ℝ) * Real.exp (2000 * r)
  exact ⟨hQpos, hreal⟩
