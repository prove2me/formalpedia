-- Prove2me | solution 1 for section5_finite_window_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:39.301269+00:00
-- url     : https://prove2.me/submissions/de1ab46f-3000-4935-ab7c-a64a0525e4cf

import Mathlib
section
set_option autoImplicit false

/-! Conservative numerical budgets for the finite-Gaussian coordinate window. -/

theorem section5_window_tail_budget (n L : ℝ) (hn : 1 ≤ n) (hL : 32*n ≤ L) :
    2*n*Real.exp (-L^2/2) ≤ 1/256 := by
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hexp := Real.add_one_le_exp (L^2/2)
  have hden : 512*n ≤ Real.exp (L^2/2) := by nlinarith [sq_nonneg (L-32*n)]
  rw [show -L^2/2=-(L^2/2) by ring,Real.exp_neg,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem section5_window_strip_budget (n ζ : ℝ) (hn : 1 ≤ n) (hζ : 0 ≤ ζ)
    (hsmall : ζ*n ≤ 1/512) :
    2*(ζ*Real.sqrt n)/Real.sqrt (2*Real.pi) ≤ 1/256 := by
  have hsqrt : Real.sqrt n ≤ n := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ n),Real.sqrt_nonneg n]
  have hden : 1 ≤ Real.sqrt (2*Real.pi) := by
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi),
      Real.sqrt_nonneg (2*Real.pi),Real.two_le_pi]
  calc
    _ ≤ 2*(ζ*Real.sqrt n) := div_le_self (by positivity) hden
    _ ≤ _ := by nlinarith

theorem section5_window_round_budget (n M : ℝ) (hn : 1 ≤ n)
    (hM : 1073741824*n^2 ≤ M) : Real.sqrt (8*n/M) ≤ 1/256 := by
  have hM0 : 0 < M := by nlinarith [sq_nonneg (n-1)]
  have hratio : 8*n/M ≤ (1/256:ℝ)^2 := by
    apply (div_le_iff₀ hM0).mpr
    nlinarith [sq_nonneg (n-1)]
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8*n/M),Real.sqrt_nonneg (8*n/M)]

theorem section5_window_sampling_budget (n M : ℝ) (hn : 1 ≤ n)
    (hM : 1073741824*n^2 ≤ M) :
    8*n*Real.sqrt (32/M) ≤ 1/256 ∧
      4*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) ≤ 1/256 := by
  have hn0 : 0 < n := by linarith
  have hM0 : 0 < M := by nlinarith [sq_nonneg (n-1)]
  constructor
  · have hr : 32/M ≤ (1/(2048*n))^2 := by
      rw [div_pow]
      apply (div_le_div_iff₀ hM0 (by positivity : 0 < (2048*n)^2)).mpr
      nlinarith
    have hs : Real.sqrt (32/M) ≤ 1/(2048*n) := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 32/M),Real.sqrt_nonneg (32/M),
        show (0:ℝ) < 1/(2048*n) by positivity]
    calc
      _ ≤ 8*n*(1/(2048*n)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by field_simp; norm_num
  · have hsqrt : Real.sqrt (2*n) ≤ 2*n := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*n),Real.sqrt_nonneg (2*n)]
    have hexp := Real.add_one_le_exp (Real.pi*M/4)
    have hden : 1024*Real.sqrt (2*n) ≤ Real.exp (Real.pi*M/4) := by
      have hh : 4096*n ≤ M := by nlinarith [sq_nonneg (n-1)]
      nlinarith [mul_le_mul_of_nonneg_right Real.two_le_pi hM0.le]
    rw [show -Real.pi*M/4=-(Real.pi*M/4) by ring,Real.exp_neg,← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith



end
set_option autoImplicit false
theorem solution (n M L ζ : ℝ) (hn : 1 ≤ n)
    (hM : 1073741824*n^2 ≤ M) (hL : 32*n ≤ L) (hζ : 0 ≤ ζ) (hsmall : ζ*n ≤ 1/512) :
    Real.sqrt (8*n/M)+2*n*Real.exp (-L^2/2)+
      2*(ζ*Real.sqrt n)/Real.sqrt (2*Real.pi)+
      (8*n*Real.sqrt (32/M)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4)) ≤ 1/32 := by
  have h1 := section5_window_round_budget n M hn hM
  have h2 := section5_window_tail_budget n L hn hL
  have h3 := section5_window_strip_budget n ζ hn hζ hsmall
  have h4 := section5_window_sampling_budget n M hn hM
  linarith
