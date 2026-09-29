-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T06:10:50.281306+00:00
-- url     : https://prove2.me/submissions/316e33ca-7d94-4901-8e62-d2bcd00c23d8

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_bernoulli_event_probability_mono
import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

namespace Bot5_minpoint

/-! Local copy of the `_min_dim` scale-absorption (proved axiom-clean in
Scratch_min_absorb.lean) plus helpers, so this consumer is self-contained. -/

theorem beta_log_ge_one (β : ℝ) (hβ : 2 < β) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ β * Real.log x := by
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (1:ℝ) ≤ 2 * Real.log 2 := by
    rw [show (2:ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_three
    linarith
  calc (1:ℝ) ≤ 2 * Real.log 2 := h4
    _ ≤ β * Real.log x := by
        apply mul_le_mul (le_of_lt hβ) hlog2 (le_of_lt hlog2pos) (by linarith)

theorem min_mul_max_real (n₁ n₂ : ℕ) :
    (↑(min n₁ n₂) : ℝ) * (↑(max n₁ n₂) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
  rw [← Nat.cast_mul]; exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (min_mul_max n₁ n₂)

theorem rpow_three_half (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x ((3:ℝ)/2) = x * Real.sqrt x := by
  have h1 : Real.rpow x ((3:ℝ)/2) = Real.sqrt (x ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
    norm_num
  rw [h1, show x ^ 3 = x ^ 2 * x by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx]

theorem min_scale_absorption
    (Cbern Centry Cfro : ℝ) (hCbern : 0 < Cbern) (hCentry : 0 < Centry) (hCfro : 0 < Cfro)
    (β lam : ℝ) (hβ : 2 < β) (hlam : 1 ≤ lam)
    (n₁ n₂ r m : ℕ) (μ₀ : ℝ)
    (hn1 : 0 < n₁) (hn2 : 0 < n₂) (hr : 0 < r) (hm : m ≤ n₁ * n₂)
    (hμ0 : 1 ≤ μ₀)
    (hmaxge2 : (2:ℝ) ≤ (↑(max n₁ n₂) : ℝ))
    (hdens : (m : ℝ) ≥
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
          (β * Real.log (↑(max n₁ n₂)))) :
    Cbern *
        (Real.sqrt
            ((β * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) +
          ((β * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(min n₁ n₂))) ^ 2))) ≤
      (Cbern * (Cfro + Centry)) *
        Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
          Real.rpow
            ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
            ((3 : ℝ) / 2) := by
  -- abbreviations
  set X : ℝ := (↑(max n₁ n₂) : ℝ) with hX
  set Y : ℝ := (↑(min n₁ n₂) : ℝ) with hY
  set L : ℝ := β * Real.log X with hL
  have hμ0pos : 0 < μ₀ := by linarith
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r:ℝ) := by linarith
  have hlampos : 0 < lam := by linarith
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by rw [hY]; have : 0 < min n₁ n₂ := lt_min hn1 hn2; exact_mod_cast this
  have hn1R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn2
  have hLpos : 0 < L := by
    rw [hL]; have := beta_log_ge_one β hβ X hmaxge2; linarith
  -- m positivity from density
  have hμpow43 : 0 < Real.rpow μ₀ ((4:ℝ)/3) := Real.rpow_pos_of_pos hμ0pos _
  have hrpow43 : 0 < Real.rpow (r:ℝ) ((4:ℝ)/3) := Real.rpow_pos_of_pos hrpos _
  have hβpos : 0 < β := by linarith
  have hDpos : 0 < lam * Real.rpow μ₀ ((4 : ℝ) / 3) * X * Real.rpow (r : ℝ) ((4 : ℝ) / 3) * L := by
    rw [hL]; positivity
  have hmR : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hDpos hdens
  -- min·max = n₁·n₂
  have hminmax : Y * X = (n₁:ℝ) * (n₂:ℝ) := by rw [hY, hX]; exact min_mul_max_real n₁ n₂
  have hmle : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
  have hmleXY : (m:ℝ) ≤ X * Y := by rw [mul_comm]; exact le_trans hmle (le_of_eq hminmax.symm)
  -- p = m/(n₁n₂); 1/p = X·Y/m
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  have hple1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; exact hmle
  have hpinv : p⁻¹ = X * Y / (m:ℝ) := by
    rw [hp, inv_div, ← hminmax]; ring
  -- density ⟹ Y ≥ μ₀·r·L   (and the cruder Y ≥ μ₀ r L is all we need for term 2)
  have hYbound : μ₀ * (r:ℝ) * L ≤ Y := by
    -- from m ≤ X·Y and m ≥ lam μ₀^{4/3} X r^{4/3} L : Y ≥ lam μ₀^{4/3} r^{4/3} L ≥ μ₀ r L
    have hdens' : lam * Real.rpow μ₀ ((4:ℝ)/3) * X * Real.rpow (r:ℝ) ((4:ℝ)/3) * L ≤ (m:ℝ) :=
      hdens
    have hchain : lam * Real.rpow μ₀ ((4:ℝ)/3) * X * Real.rpow (r:ℝ) ((4:ℝ)/3) * L ≤ X * Y :=
      le_trans hdens' hmleXY
    -- divide by X > 0
    have hYge : lam * Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) * L ≤ Y := by
      have hX' : 0 < X := hXpos
      nlinarith [hchain, hX', mul_pos (mul_pos hlampos hμpow43) hrpow43, hLpos]
    -- μ₀^{4/3} ≥ μ₀, r^{4/3} ≥ r, lam ≥ 1
    have hμ43 : μ₀ ≤ Real.rpow μ₀ ((4:ℝ)/3) := by
      have := Real.rpow_le_rpow_left_iff (x := μ₀) (y := (1:ℝ)) (z := (4:ℝ)/3)
      calc μ₀ = Real.rpow μ₀ 1 := (Real.rpow_one μ₀).symm
        _ ≤ Real.rpow μ₀ ((4:ℝ)/3) := by
            apply Real.rpow_le_rpow_of_exponent_le hμ0 (by norm_num)
    have hr43 : (r:ℝ) ≤ Real.rpow (r:ℝ) ((4:ℝ)/3) := by
      calc (r:ℝ) = Real.rpow (r:ℝ) 1 := (Real.rpow_one (r:ℝ)).symm
        _ ≤ Real.rpow (r:ℝ) ((4:ℝ)/3) := by
            apply Real.rpow_le_rpow_of_exponent_le hrR (by norm_num)
    have hstep : μ₀ * (r:ℝ) * L ≤ lam * Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) * L := by
      have h1 : μ₀ * (r:ℝ) ≤ lam * Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) := by
        calc μ₀ * (r:ℝ) ≤ Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) :=
              mul_le_mul hμ43 hr43 (by linarith) (le_of_lt hμpow43)
          _ ≤ lam * (Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3)) := by
              nlinarith [mul_pos hμpow43 hrpow43, hlam]
          _ = lam * Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) := by ring
      nlinarith [h1, hLpos]
    linarith [hstep, hYge]
  -- Output S := rpow(μ₀ X r/m)(3/2) ≥ 0
  set q : ℝ := μ₀ * X * (r:ℝ) / (m:ℝ) with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  set S : ℝ := Real.rpow q ((3:ℝ)/2) with hS
  have hSpos : 0 < S := by rw [hS]; exact Real.rpow_pos_of_pos hqpos _
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  -- Convert RHS factor to √L · S form; the goal RHS is (Cbern(Cfro+Centry))·√L·S.
  -- Bound each summand.
  -- ===== TERM 1 (sub-gaussian) =====
  -- √(L/p)·(Cfro·μ₀^{3/2}·(r/Y)^{3/2}) ≤ Cfro·√L·S
  have hT1 : Real.sqrt (L / p) *
      (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2))
        ≤ Cfro * (Real.sqrt L * S) := by
    -- nonneg of inner factor
    have hrpμ : 0 ≤ Real.rpow μ₀ ((3:ℝ)/2) := Real.rpow_nonneg (le_of_lt hμ0pos) _
    have hrprY : 0 ≤ Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2) := Real.rpow_nonneg (by positivity) _
    have hinner_nn : 0 ≤ Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2) :=
      mul_nonneg hrpμ hrprY
    -- It suffices (divide Cfro > 0): √(L/p)·μ₀^{3/2}·(r/Y)^{3/2} ≤ √L·S
    rw [show Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)
          = Cfro * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)) by ring,
        show Real.sqrt (L/p) * (Cfro * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)))
          = Cfro * (Real.sqrt (L/p) * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2))) by ring]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCfro)
    -- core: √(L/p)·μ₀^{3/2}·(r/Y)^{3/2} ≤ √L·S, both nonneg ⇒ compare squares
    have hLHS_nn : 0 ≤ Real.sqrt (L/p) * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)) :=
      mul_nonneg (Real.sqrt_nonneg _) hinner_nn
    have hRHS_nn : 0 ≤ Real.sqrt L * S := by positivity
    rw [← Real.sqrt_sq hRHS_nn, ← Real.sqrt_sq hLHS_nn]
    apply Real.sqrt_le_sqrt
    -- square both sides
    have he_lhs : (Real.sqrt (L/p) * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)))^2
        = (L/p) * (μ₀^3 * ((r:ℝ)/Y)^3) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [mul_pow]
      rw [show (Real.rpow μ₀ ((3:ℝ)/2))^2 = μ₀^3 by
            rw [rpow_three_half μ₀ (le_of_lt hμ0pos)]; rw [mul_pow, Real.sq_sqrt (le_of_lt hμ0pos)]; ring,
          show (Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2))^2 = ((r:ℝ)/Y)^3 by
            rw [rpow_three_half ((r:ℝ)/Y) (by positivity)]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring]
    have he_rhs : (Real.sqrt L * S)^2 = L * q^3 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hLpos), hS]
      rw [show (Real.rpow q ((3:ℝ)/2))^2 = q^3 by
            rw [rpow_three_half q (le_of_lt hqpos)]; rw [mul_pow, Real.sq_sqrt (le_of_lt hqpos)]; ring]
    rw [he_lhs, he_rhs, hq]
    -- (L/p)·μ₀³(r/Y)³ ≤ L·q³, q = μ₀ X r/m, 1/p = XY/m
    -- Reduce to: μ₀³(r/Y)³ ≤ q³·p   (then multiply by L>0, and L/p = L·p⁻¹)
    have key : μ₀^3 * ((r:ℝ)/Y)^3 ≤ (μ₀ * X * (r:ℝ)/(m:ℝ))^3 * p := by
      have hpval : p = (m:ℝ) / (X * Y) := by
        rw [hp, ← hminmax]; rw [mul_comm Y X]
      rw [hpval]
      have hmsq : (m:ℝ)^2 ≤ X^2 * Y^2 := by nlinarith [hmleXY, hmR, hXpos, hYpos]
      -- LHS = μ₀³r³/Y³ ; RHS = (μ₀Xr)³/m³ · (m/(XY)) = μ₀³X³r³/m³ · m/(XY)
      have hlhs_eq : μ₀^3 * ((r:ℝ)/Y)^3 = (μ₀^3 * (r:ℝ)^3) / Y^3 := by
        rw [div_pow]; ring
      have hrhs_eq : (μ₀ * X * (r:ℝ)/(m:ℝ))^3 * ((m:ℝ)/(X*Y))
          = (μ₀^3 * X^2 * (r:ℝ)^3) / ((m:ℝ)^2 * Y) := by
        rw [div_pow]; field_simp
      rw [hlhs_eq, hrhs_eq]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- goal: μ₀³r³ · (m²·Y) ≤ μ₀³X²r³ · Y³.  Factor μ₀³r³Y > 0, reduce to m² ≤ X²Y².
      have hfac : 0 ≤ μ₀^3 * (r:ℝ)^3 * Y :=
        le_of_lt (mul_pos (mul_pos (pow_pos hμ0pos 3) (pow_pos hrpos 3)) hYpos)
      nlinarith [mul_le_mul_of_nonneg_left hmsq hfac, hYpos, sq_nonneg Y,
        mul_pos (pow_pos hμ0pos 3) (pow_pos hrpos 3)]
    have hLp : L / p = L * p⁻¹ := by rw [div_eq_mul_inv]
    rw [hLp]
    calc L * p⁻¹ * (μ₀^3 * ((r:ℝ)/Y)^3)
        ≤ L * p⁻¹ * ((μ₀ * X * (r:ℝ)/(m:ℝ))^3 * p) := by
          apply mul_le_mul_of_nonneg_left key (by positivity)
      _ = L * (μ₀ * X * (r:ℝ)/(m:ℝ))^3 := by
          have : p⁻¹ * p = 1 := inv_mul_cancel₀ (ne_of_gt hppos)
          field_simp
  -- ===== TERM 2 (sub-exp) =====
  -- (L/p)·(Centry·μ₀²·(r/Y)²) ≤ Centry·√L·S
  have hT2 : (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))
        ≤ Centry * (Real.sqrt L * S) := by
    rw [show Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)
          = Centry * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)) by ring,
        show (L / p) * (Centry * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)))
          = Centry * ((L / p) * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))) by ring]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCentry)
    -- core: (L/p)·μ₀²(r/Y)² ≤ √L·S, both nonneg ⇒ compare squares
    have hLHS_nn : 0 ≤ (L / p) * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)) := by positivity
    have hRHS_nn : 0 ≤ Real.sqrt L * S := by positivity
    rw [← Real.sqrt_sq hRHS_nn, ← Real.sqrt_sq hLHS_nn]
    apply Real.sqrt_le_sqrt
    -- square both sides
    have he_rhs : (Real.sqrt L * S)^2 = L * q^3 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hLpos), hS]
      rw [show (Real.rpow q ((3:ℝ)/2))^2 = q^3 by
            rw [rpow_three_half q (le_of_lt hqpos)]; rw [mul_pow, Real.sq_sqrt (le_of_lt hqpos)]; ring]
    rw [he_rhs, hq]
    -- LHS² = (L/p)²·μ₀⁴(r/Y)⁴ ; need ≤ L·(μ₀ X r/m)³
    -- Substitute 1/p = XY/m.
    have hpval : (1:ℝ)/p = X * Y / (m:ℝ) := by rw [one_div]; exact hpinv
    have hLHS_eq : ((L / p) * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)))^2
        = L^2 * (X*Y/(m:ℝ))^2 * (μ₀^4 * (r:ℝ)^4 / Y^4) := by
      rw [div_eq_mul_inv L p, ← one_div, hpval]
      rw [div_pow]
      ring
    rw [hLHS_eq]
    -- target: L²·(XY/m)²·μ₀⁴r⁴/Y⁴ ≤ L·(μ₀ X r/m)³
    have hrhs_eq2 : L * (μ₀ * X * (r:ℝ)/(m:ℝ))^3 = L * (μ₀^3 * X^3 * (r:ℝ)^3) / (m:ℝ)^3 := by
      rw [div_pow]; ring
    have hlhs_eq2 : L^2 * (X*Y/(m:ℝ))^2 * (μ₀^4 * (r:ℝ)^4 / Y^4)
        = (L^2 * X^2 * μ₀^4 * (r:ℝ)^4) / ((m:ℝ)^2 * Y^2) := by
      rw [div_pow]; field_simp
    rw [hrhs_eq2, hlhs_eq2]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- (L²X²μ₀⁴r⁴)·m³ ≤ L·μ₀³X³r³·(m²Y²)
    -- cancel L·μ₀³X²r³·m² : L·μ₀·r·m ≤ X·Y²
    have hkey2 : L * μ₀ * (r:ℝ) * (m:ℝ) ≤ X * Y^2 := by
      -- m ≤ XY and Y ≥ μ₀ r L  ⟹ L μ₀ r m ≤ L μ₀ r X Y ≤ Y · X Y = X Y²
      have h1 : L * μ₀ * (r:ℝ) * (m:ℝ) ≤ L * μ₀ * (r:ℝ) * (X * Y) :=
        mul_le_mul_of_nonneg_left hmleXY (by positivity)
      have h2 : L * μ₀ * (r:ℝ) * (X * Y) ≤ Y * (X * Y) := by
        have hYb : μ₀ * (r:ℝ) * L ≤ Y := hYbound
        have : L * μ₀ * (r:ℝ) ≤ Y := by rw [show L * μ₀ * (r:ℝ) = μ₀ * (r:ℝ) * L by ring]; exact hYb
        apply mul_le_mul_of_nonneg_right this (by positivity)
      calc L * μ₀ * (r:ℝ) * (m:ℝ) ≤ L * μ₀ * (r:ℝ) * (X * Y) := h1
        _ ≤ Y * (X * Y) := h2
        _ = X * Y^2 := by ring
    -- multiply hkey2 by L·μ₀³X²r³·m² ≥ 0 and assemble
    have hfac2 : 0 ≤ L * μ₀^3 * X^2 * (r:ℝ)^3 * (m:ℝ)^2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkey2 hfac2, hLpos, hXpos, hYpos, hmR,
      pow_pos hμ0pos 3, pow_pos hrpos 3]
  -- ===== COMBINE =====
  -- goal LHS = Cbern·(Term1 + Term2) ;  Term1 ≤ Cfro·√L·S, Term2 ≤ Centry·√L·S
  have hsum : Real.sqrt (L / p) *
        (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2)) +
      (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))
        ≤ (Cfro + Centry) * (Real.sqrt L * S) := by
    have := add_le_add hT1 hT2
    calc Real.sqrt (L / p) *
          (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2)) +
        (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))
          ≤ Cfro * (Real.sqrt L * S) + Centry * (Real.sqrt L * S) := this
      _ = (Cfro + Centry) * (Real.sqrt L * S) := by ring
  -- Now wire to the actual goal (which uses ↑(max), ↑(min), p spelled out).
  have hgoal_lhs : Cbern *
      (Real.sqrt ((β * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) +
        ((β * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 2)))
      = Cbern * (Real.sqrt (L / p) *
        (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2)) +
      (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))) := by
    rw [← hX, ← hY, ← hL, ← hp]
  rw [hgoal_lhs]
  have hgoal_rhs : (Cbern * (Cfro + Centry)) *
        Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
          Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2)
      = Cbern * ((Cfro + Centry) * (Real.sqrt L * S)) := by
    rw [← hX, ← hL, ← hq, ← hS]; ring
  rw [hgoal_rhs]
  apply mul_le_mul_of_nonneg_left hsum (le_of_lt hCbern)

/-- `bernoulliEventProb` is nonnegative for `0 ≤ p ≤ 1`. -/
theorem bernoulliEventProb_nonneg {n1 n2 : Nat} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Prop) :
    0 ≤ bernoulliEventProb p Event := by
  unfold bernoulliEventProb
  apply Finset.sum_nonneg
  intro Omega _
  by_cases h : Event Omega
  · rw [if_pos h]; unfold bernoulliObservationWeight
    apply mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  · rw [if_neg h]

end Bot5_minpoint

open Bot5_minpoint

/-- The `_min_dim` pointwise mean-coefficient tail consumer: same conclusion as the
Proved max-form node `44fc7aa8`, but consuming bot6's `(r/min)` base bounds.
Reduces onto the Proved parametric Bernstein engine `3cbb6b11` + the `_min_dim`
scale-absorption (`min_scale_absorption`) + `bernoulli_event_probability_mono`. -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ w1 : Fin n₁ × Fin n₂,
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctMeanCoefficient Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        entrySupNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(min n₁ n₂))) ^ 2) →
        frobeniusNorm
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                Cpoint *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  obtain ⟨Cbern, cbern, hCbern, hcbern, hengine⟩ :=
    scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
  refine ⟨Cbern * (Cfro + Centry), cbern + 1, by positivity, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ0 hμ1 hA0 hA1 hdens w1
  intro hmeaneq hentry hfrob
  -- p, basic facts
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn1R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn2
  have hmle : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; exact hmle
  -- base matrix abbreviation
  set B : Matrix (Fin n₁) (Fin n₂) ℝ :=
    quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 with hB
  set Coeff : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega => quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1 with hCoeff
  -- engine instance: Coeff = matrixEntrySum (centeredSamplingFluctuation Omega p B)
  have hCoeffeq : ∀ Omega, Coeff Omega =
      matrixEntrySum (centeredSamplingFluctuation Omega p B) := by
    intro Omega; rw [hCoeff, hB, hp]; exact hmeaneq Omega
  have hentry' : entrySupNorm B ≤ Centry * μ₀ ^ 2 * (((r:ℝ)/(↑(min n₁ n₂)))^2) := by
    rw [hB]; exact hentry
  have hfrob' : frobeniusNorm B ≤
      Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/(↑(min n₁ n₂))) ((3:ℝ)/2) := by
    rw [hB]; exact hfrob
  -- engine output (Bernstein expression event)
  have hev := hengine β hβ n₁ n₂ m hn1 hn2 hm Coeff B
      (Centry * μ₀ ^ 2 * (((r:ℝ)/(↑(min n₁ n₂)))^2))
      (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/(↑(min n₁ n₂))) ((3:ℝ)/2))
      hCoeffeq hentry' hfrob'
  -- abbreviate the engine event RHS and the target RHS
  set BernExpr : ℝ := Cbern *
      (Real.sqrt ((β * Real.log (↑(max n₁ n₂))) / p) *
        (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/(↑(min n₁ n₂))) ((3:ℝ)/2)) +
        ((β * Real.log (↑(max n₁ n₂))) / p) *
        (Centry * μ₀ ^ 2 * (((r:ℝ)/(↑(min n₁ n₂)))^2))) with hBE
  set TargetExpr : ℝ := (Cbern * (Cfro + Centry)) *
      Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
        Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r:ℝ)) / (m:ℝ)) ((3:ℝ)/2) with hTE
  -- Case split on max ≥ 2 vs the 1×1 corner.
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hmaxsmall | hmaxbig
  · -- max < 2 ⟹ max = 1 ⟹ log max = 0 ⟹ target bound is vacuous (1 - cpoint ≤ 0 ≤ prob).
    have hmax1 : max n₁ n₂ = 1 := by
      have := lt_of_lt_of_le hn1 (le_max_left n₁ n₂); omega
    have hlog0 : Real.log (↑(max n₁ n₂)) = 0 := by rw [hmax1]; simp
    have hrpow1 : Real.rpow (↑(max n₁ n₂)) (-β) = 1 := by
      rw [hmax1]; simp
    rw [hrpow1, mul_one]
    have hprobnn : 0 ≤ bernoulliEventProb p
        (fun Omega => |Coeff Omega| ≤ TargetExpr) :=
      bernoulliEventProb_nonneg p hp0 hp1 _
    -- need: 1 - (cbern+1) ≤ that prob; since cbern>0, 1-(cbern+1) = -cbern < 0 ≤ prob.
    have : (1:ℝ) - (cbern + 1) ≤ 0 := by linarith
    -- but the goal's event uses the spelled-out Coeff/TargetExpr; rewrite.
    show (1:ℝ) - (cbern + 1) ≤ bernoulliEventProb p _
    refine le_trans this ?_
    apply bernoulliEventProb_nonneg p hp0 hp1
  · -- max ≥ 2: genuine Bernstein + absorption + mono.
    have hmaxge2 : (2:ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmaxbig
    -- absorption: BernExpr ≤ TargetExpr
    have habs : BernExpr ≤ TargetExpr := by
      rw [hBE, hTE]
      exact min_scale_absorption Cbern Centry Cfro hCbern hCentry hCfro β lam hβ hlam
        n₁ n₂ r m μ₀ hn1 hn2 hr hm hμ0 hmaxge2 hdens
    -- mono: widen engine event (|Coeff| ≤ BernExpr) to target (|Coeff| ≤ TargetExpr)
    have hmono := bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
      (fun Omega => |Coeff Omega| ≤ BernExpr)
      (fun Omega => |Coeff Omega| ≤ TargetExpr)
      hp0 hp1 (fun Omega h => le_trans h habs)
    -- engine gives:  bernoulliEventProb p (|Coeff| ≤ BernExpr) ≥ 1 - cbern·max^{-β}
    -- hev's event RHS is literally BernExpr (after unfolding p in the engine).
    have hev' : bernoulliEventProb p (fun Omega => |Coeff Omega| ≤ BernExpr) ≥
        1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
      rw [hBE]; exact hev
    have hcbern1 : 1 - (cbern + 1) * Real.rpow (↑(max n₁ n₂)) (-β) ≤
        1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
      have hrnn : 0 ≤ Real.rpow (↑(max n₁ n₂)) (-β) := Real.rpow_nonneg (by positivity) _
      nlinarith [hrnn]
    calc 1 - (cbern + 1) * Real.rpow (↑(max n₁ n₂)) (-β)
        ≤ 1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := hcbern1
      _ ≤ bernoulliEventProb p (fun Omega => |Coeff Omega| ≤ BernExpr) := hev'
      _ ≤ bernoulliEventProb p (fun Omega => |Coeff Omega| ≤ TargetExpr) := hmono
