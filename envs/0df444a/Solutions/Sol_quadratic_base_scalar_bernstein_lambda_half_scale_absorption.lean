-- Prove2me | solution 1 for quadratic_base_scalar_bernstein_lambda_half_scale_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T18:58:09.528022+00:00
-- url     : https://prove2.me/submissions/ce50a697-aa2c-46c5-b060-c9f2789b4d63

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 800000

namespace Provef27

theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-- `1 ≤ β log n` for `β > 2`, `n ≥ 2`. -/
theorem one_le_beta_log (β n : ℝ) (hβ : 2 < β) (hn : 2 ≤ n) (hlogpos : 0 < Real.log n) :
    (1:ℝ) ≤ β * Real.log n := by
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have h4 : (1:ℝ) < Real.log 4 := by
    have : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
    calc (1:ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [hlog2n, hlogpos, h4, hlog4]

/-- √(x^(4/3)) = x^(2/3). -/
theorem sqrt_rpow43 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.rpow x ((4:ℝ)/3)) = Real.rpow x ((2:ℝ)/3) := by
  rw [Real.sqrt_eq_rpow]
  show (x ^ ((4:ℝ)/3)) ^ ((1:ℝ)/2) = x ^ ((2:ℝ)/3)
  rw [← Real.rpow_mul hx]; norm_num

/-- x^(3/2) = x^(2/3) · x^(5/6). -/
theorem rpow32_split (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x ((3:ℝ)/2) = Real.rpow x ((2:ℝ)/3) * Real.rpow x ((5:ℝ)/6) := by
  show x ^ ((3:ℝ)/2) = x ^ ((2:ℝ)/3) * x ^ ((5:ℝ)/6)
  rw [← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]; norm_num

/-- x^2 = x^(4/3) · x^(2/3). -/
theorem rpow2_split (x : ℝ) (hx : 0 ≤ x) :
    x^2 = Real.rpow x ((4:ℝ)/3) * Real.rpow x ((2:ℝ)/3) := by
  rw [show (x^2) = x^(2:ℝ) by rw [Real.rpow_two]]
  show x ^ (2:ℝ) = x ^ ((4:ℝ)/3) * x ^ ((2:ℝ)/3)
  rw [← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]; norm_num

end Provef27

open Provef27 in
/-- `quadratic_base_scalar_bernstein_lambda_half_scale_absorption`.
Pure scalar scale-absorption: the quadratic base Bernstein scale is `O(λ^{-1/2})`. -/
theorem solution
    (Cbern Centry Cfro : ℝ) :
    0 < Cbern → 0 < Centry → 0 < Cfro →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbern *
            (Real.sqrt
                ((β * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
                Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) +
              ((β * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Centry * μ₀ ^ 2 *
                (((r : ℝ) / (↑(max n₁ n₂))) ^ 2))) ≤
          Cpoint * Real.rpow lam (-((1 : ℝ) / 2)) := by
  intro hCbern hCentry hCfro
  refine ⟨Cbern * (Cfro + Centry), by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn_def
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  set L : ℝ := β * Real.log n with hL_def
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  -- x = μ₀ r ≥ 1
  set x : ℝ := μ₀ * (r:ℝ) with hx_def
  have hx1 : (1:ℝ) ≤ x := by rw [hx_def]; nlinarith
  have hxpos : (0:ℝ) < x := by linarith
  -- lam^(-1/2) ≥ 0
  have hlamhalf_pos : (0:ℝ) < Real.rpow lam (-((1:ℝ)/2)) := by
    rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hsmall | hbig
  · -- n=1: log n = 0 ⇒ the whole bracket is 0
    have hmaxeq : max n₁ n₂ = 1 := by have := le_max_left n₁ n₂; omega
    have hnval : n = 1 := by rw [hn_def, hmaxeq]; norm_num
    have hLval : L = 0 := by rw [hL_def, hnval]; simp
    rw [hLval]
    have hrhs0 : (0:ℝ) ≤ Cbern * (Cfro + Centry) * Real.rpow lam (-((1:ℝ)/2)) := by positivity
    simp only [zero_div, Real.sqrt_zero, zero_mul, zero_add, mul_zero]
    exact hrhs0
  · -- main case n≥2
    have hn2le : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hbig
    have hnpos : (0:ℝ) < n := by linarith
    have hlogpos : (0:ℝ) < Real.log n := Real.log_pos (by linarith)
    have hL1 : (1:ℝ) ≤ L := by rw [hL_def]; exact one_le_beta_log β n hβ hn2le hlogpos
    have hLpos : (0:ℝ) < L := by linarith
    -- feasibility: x^(4/3) ≤ n
    set D : ℝ := Real.rpow x ((4:ℝ)/3) with hD_def
    have hcombine : Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) = D := by
      rw [hD_def, hx_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) (le_of_lt hrR)]
    have hD1 : (1:ℝ) ≤ D := by
      rw [hD_def, rpow_eq]
      calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := by rw [Real.one_rpow]
        _ ≤ x ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
    have hDpos : (0:ℝ) < D := by linarith
    -- m ≥ lam * D * n * L
    have hsample' : (m:ℝ) ≥ lam * D * n * L := by
      have heq : lam * D * n * L
          = lam * Real.rpow μ₀ ((4:ℝ)/3) * n * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log n) := by
        rw [← hcombine, hL_def]; ring
      rw [heq, ← hn_def] at *; exact hsample
    have hlbpos : (0:ℝ) < lam * D * n * L := by positivity
    have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hlbpos hsample'
    have hppos : (0:ℝ) < p := by rw [hp_def]; positivity
    -- feasibility D ≤ n :  lam D n L ≤ m ≤ n₁n₂ ≤ n²
    have hfeas : D ≤ n := by
      have hmle : (m:ℝ) ≤ n^2 := by
        have h1 : (n₁:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_left _ _
        have h2 : (n₂:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_right _ _
        have : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
        nlinarith [this, hn₁R, hn₂R, h1, h2]
      -- lam D n L ≤ n² and lam,L ≥ 1 ⇒ D n ≤ n² ⇒ D ≤ n
      have hDnL : lam * D * n * L ≤ n^2 := le_trans hsample' hmle
      have hDn_le : D * n ≤ n * n := by
        have hDnpos : (0:ℝ) ≤ D * n := by positivity
        have hlamL1 : (1:ℝ) ≤ lam * L := by nlinarith [hlam, hL1, hlam0, hLpos]
        have hexp : D * n ≤ lam * D * n * L := by
          nlinarith [mul_nonneg hDnpos (by linarith : (0:ℝ) ≤ lam * L - 1)]
        nlinarith [hexp, hDnL]
      exact le_of_mul_le_mul_right hDn_le hnpos
    -- L/p ≤ n/(lam x^(4/3)) = n/(lam D)
    have hn1n2 : (n₁:ℝ) * (n₂:ℝ) ≤ n^2 := by
      have h1 : (n₁:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_left _ _
      have h2 : (n₂:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_right _ _
      nlinarith [hn₁R, hn₂R]
    have hLp_le : L / p ≤ n / (lam * D) := by
      rw [hp_def, div_div_eq_mul_div]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- (L * (n₁n₂)) * (lam D) ≤ n * m
      have hmge : lam * D * n * L ≤ (m:ℝ) := hsample'
      nlinarith [hmge, hn1n2, hLpos, hDpos, hlam0, hnpos, hn₁R, hn₂R,
        mul_pos hlam0 hDpos, mul_pos hLpos (mul_pos hlam0 hDpos)]
    have hLp_pos : (0:ℝ) < L / p := by positivity
    have hLp_nn : (0:ℝ) ≤ L / p := le_of_lt hLp_pos
    -- ===== TERM 1 =====
    -- √(L/p) * (μ₀^(3/2) (r/n)^(3/2)) ≤ ... ≤ Cfro-free: bound the prefactor
    -- (μ₀^(3/2))·((r/n)^(3/2)) = (μ₀ (r/n))^(3/2) = (x/n)^(3/2)
    have hrn_nn : (0:ℝ) ≤ (r:ℝ)/n := by positivity
    have hmerge32 : Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)
        = Real.rpow (x / n) ((3:ℝ)/2) := by
      rw [hx_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) hrn_nn,
        mul_div_assoc]
    -- (x/n)^(3/2) = x^(3/2)/n^(3/2)
    have hxn32 : Real.rpow (x / n) ((3:ℝ)/2) = Real.rpow x ((3:ℝ)/2) / Real.rpow n ((3:ℝ)/2) := by
      rw [rpow_eq, rpow_eq, rpow_eq, Real.div_rpow (le_of_lt hxpos) (le_of_lt hnpos)]
    -- √(L/p) ≤ √(n/(lam D))
    have hsqrtLp : Real.sqrt (L / p) ≤ Real.sqrt (n / (lam * D)) :=
      Real.sqrt_le_sqrt hLp_le
    -- √(n/(lam D)) = √n / (√lam · x^(2/3))    [since √D = x^(2/3)]
    have hsqrtD : Real.sqrt D = Real.rpow x ((2:ℝ)/3) := by
      rw [hD_def]; exact sqrt_rpow43 x (le_of_lt hxpos)
    have hsqrt_nlamD : Real.sqrt (n / (lam * D)) = Real.sqrt n / (Real.sqrt lam * Real.rpow x ((2:ℝ)/3)) := by
      rw [Real.sqrt_div' n (by positivity), Real.sqrt_mul (le_of_lt hlam0), hsqrtD]
    -- positivity facts
    have hx23pos : (0:ℝ) < Real.rpow x ((2:ℝ)/3) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hxpos _
    have hx56pos : (0:ℝ) < Real.rpow x ((5:ℝ)/6) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hxpos _
    have hsqrtlam_pos : (0:ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
    have hsqrtn_pos : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    -- lam^(-1/2) = 1/√lam
    have hlamhalf_eq : Real.rpow lam (-((1:ℝ)/2)) = 1 / Real.sqrt lam := by
      rw [Real.sqrt_eq_rpow]
      show lam ^ (-((1:ℝ)/2)) = 1 / lam ^ ((1:ℝ)/2)
      rw [Real.rpow_neg (le_of_lt hlam0), inv_eq_one_div]
    -- √n / n^(3/2) = 1/n  (n^(3/2) = n*√n)
    have hn32 : Real.rpow n ((3:ℝ)/2) = n * Real.sqrt n := by
      rw [Real.sqrt_eq_rpow]
      show n ^ ((3:ℝ)/2) = n * n ^ ((1:ℝ)/2)
      rw [show ((3:ℝ)/2) = 1 + (1:ℝ)/2 by norm_num, Real.rpow_add hnpos, Real.rpow_one]
    have hn32pos : (0:ℝ) < Real.rpow n ((3:ℝ)/2) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hnpos _
    -- x^(4/3) ≤ n  is hfeas (D = x^(4/3))
    have hfeas' : Real.rpow x ((4:ℝ)/3) ≤ n := by rw [← hD_def]; exact hfeas
    -- x^(5/6) ≤ x^(4/3) ≤ n
    have hx56_le_n : Real.rpow x ((5:ℝ)/6) ≤ n := by
      calc Real.rpow x ((5:ℝ)/6) ≤ Real.rpow x ((4:ℝ)/3) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ ≤ n := hfeas'
    -- x^(2/3) ≤ x^(4/3) ≤ n
    have hx23_le_n : Real.rpow x ((2:ℝ)/3) ≤ n := by
      calc Real.rpow x ((2:ℝ)/3) ≤ Real.rpow x ((4:ℝ)/3) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ ≤ n := hfeas'
    -- ============ TERM 1 BOUND ============
    -- Term1' = √(L/p) * (Cfro * x^(3/2)/n^(3/2))
    have hterm1 :
        Real.sqrt (L / p) * (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2))
          ≤ Cfro * Real.rpow lam (-((1:ℝ)/2)) := by
      -- rewrite the μ₀,(r/n) product
      have hmul32 : Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)
          = Real.rpow x ((3:ℝ)/2) / Real.rpow n ((3:ℝ)/2) := by rw [hmerge32, hxn32]
      have hstep1 :
          Real.sqrt (L / p) * (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2))
            = Cfro * (Real.sqrt (L / p) * (Real.rpow x ((3:ℝ)/2) / Real.rpow n ((3:ℝ)/2))) := by
        rw [mul_assoc, hmul32]; ring
      rw [hstep1, hlamhalf_eq]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCfro)
      -- √(L/p) * (x^(3/2)/n^(3/2)) ≤ 1/√lam
      calc Real.sqrt (L / p) * (Real.rpow x ((3:ℝ)/2) / Real.rpow n ((3:ℝ)/2))
          ≤ (Real.sqrt n / (Real.sqrt lam * Real.rpow x ((2:ℝ)/3)))
              * (Real.rpow x ((3:ℝ)/2) / Real.rpow n ((3:ℝ)/2)) := by
            have hx32pos : (0:ℝ) < Real.rpow x ((3:ℝ)/2) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hxpos _
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [← hsqrt_nlamD]; exact hsqrtLp
        _ = Real.rpow x ((5:ℝ)/6) / (Real.sqrt lam * n) := by
            rw [rpow32_split x (le_of_lt hxpos), hn32]
            rw [Real.sqrt_eq_rpow]
            field_simp
        _ ≤ n / (Real.sqrt lam * n) := by
            apply div_le_div_of_nonneg_right hx56_le_n (by positivity) |>.trans_eq rfl
        _ = 1 / Real.sqrt lam := by
            rw [mul_comm (Real.sqrt lam) n, ← div_div, div_self (ne_of_gt hnpos)]
    -- ============ TERM 2 BOUND ============
    have hterm2 :
        (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2))
          ≤ Centry * Real.rpow lam (-((1:ℝ)/2)) := by
      -- μ₀² (r/n)² = x²/n²
      have hmul2 : μ₀ ^ 2 * (((r:ℝ)/n) ^ 2) = x^2 / n^2 := by
        rw [hx_def]; rw [div_pow]; ring
      have hstep2 :
          (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2))
            = Centry * ((L / p) * (x^2 / n^2)) := by
        rw [show Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2) = Centry * (μ₀ ^ 2 * (((r:ℝ)/n) ^ 2)) by ring,
          hmul2]; ring
      rw [hstep2, hlamhalf_eq]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCentry)
      -- (L/p)*(x²/n²) ≤ 1/√lam
      have hx2pos : (0:ℝ) < x^2 := by positivity
      calc (L / p) * (x^2 / n^2)
          ≤ (n / (lam * D)) * (x^2 / n^2) := by
            apply mul_le_mul_of_nonneg_right hLp_le (by positivity)
        _ = Real.rpow x ((2:ℝ)/3) / (lam * n) := by
            rw [rpow2_split x (le_of_lt hxpos), ← hD_def]
            field_simp
        _ ≤ n / (lam * n) := by
            apply div_le_div_of_nonneg_right hx23_le_n (by positivity) |>.trans_eq rfl
        _ = 1 / lam := by
            rw [mul_comm lam n, ← div_div, div_self (ne_of_gt hnpos)]
        _ ≤ 1 / Real.sqrt lam := by
            apply div_le_div_of_nonneg_left (by norm_num) hsqrtlam_pos
            -- √lam ≤ lam   (lam ≥ 1)
            calc Real.sqrt lam ≤ Real.sqrt (lam * lam) := by
                  apply Real.sqrt_le_sqrt; nlinarith [hlam, hlam0]
              _ = lam := by rw [Real.sqrt_mul_self (le_of_lt hlam0)]
    -- ============ ASSEMBLE ============
    have hbracket :
        (Real.sqrt (L / p) *
            (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)) +
          (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2)))
          ≤ (Cfro + Centry) * Real.rpow lam (-((1:ℝ)/2)) := by
      calc _ ≤ Cfro * Real.rpow lam (-((1:ℝ)/2)) + Centry * Real.rpow lam (-((1:ℝ)/2)) :=
            add_le_add hterm1 hterm2
        _ = (Cfro + Centry) * Real.rpow lam (-((1:ℝ)/2)) := by ring
    -- the goal is already in n,p,L form (set folded it); apply the bracket bound
    have hfinal := mul_le_mul_of_nonneg_left hbracket (le_of_lt hCbern)
    calc Cbern *
            (Real.sqrt (L / p) *
              (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)) +
            (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2)))
        ≤ Cbern * ((Cfro + Centry) * Real.rpow lam (-((1:ℝ)/2))) := hfinal
      _ = Cbern * (Cfro + Centry) * Real.rpow lam (-((1:ℝ)/2)) := by ring
