-- Prove2me | solution 1 for gpy_twistedAbsWeight_sum_Icc_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T10:48:53.135479+00:00
-- url     : https://prove2.me/submissions/97f65c11-1424-4f04-8747-4386bd71b1e1

/- PubAll restated solution file: Mathlib only, absolute bounds only.
   No asymptotic TwistedMertensBound main term is stated or proved here. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def harmLogPow_aux (m : ℕ) (T : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 T, (Real.log (e : ℝ)) ^ m / (e : ℝ)

theorem log_one_add_inv_le_aux {x : ℝ} (hx : 0 < x) :
    Real.log (1 + 1 / x) ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / x by positivity)
  have h2 : (1 + 1 / x) - 1 = 1 / x := by ring
  rw [h2] at h
  exact h

theorem log_one_add_inv_ge_aux {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (1 + 1 / x) := by
  have hpos : (0 : ℝ) < x / (x + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  have hsub : x / (x + 1) - 1 = -(1 / (x + 1)) := by
    field_simp
    ring
  rw [hsub] at h
  have hinv : (1 + 1 / x) = (x / (x + 1))⁻¹ := by
    field_simp
  rw [hinv, Real.log_inv]
  linarith

theorem pow_succ_sub_pow_sandwich_aux {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (m : ℕ) :
    ((m : ℝ) + 1) * x ^ m * (y - x) ≤ y ^ (m + 1) - x ^ (m + 1)
      ∧ y ^ (m + 1) - x ^ (m + 1) ≤ ((m : ℝ) + 1) * y ^ m * (y - x) := by
  have hgeom := geom_sum₂_mul_of_ge hxy (m + 1)
  have hcard : (Finset.range (m + 1)).card = m + 1 := Finset.card_range _
  have hterm_lo : ∀ i ∈ Finset.range (m + 1),
      x ^ m ≤ y ^ i * x ^ (m + 1 - 1 - i) := by
    intro i hi
    have hi2 : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : x ^ i ≤ y ^ i := pow_le_pow_left₀ hx hxy i
    have h2 : x ^ (m + 1 - 1 - i) = x ^ (m - i) := by
      rw [show m + 1 - 1 - i = m - i by omega]
    rw [h2]
    calc x ^ m = x ^ i * x ^ (m - i) := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ y ^ i * x ^ (m - i) :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hx _)
  have hterm_hi : ∀ i ∈ Finset.range (m + 1),
      y ^ i * x ^ (m + 1 - 1 - i) ≤ y ^ m := by
    intro i hi
    have hi2 : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : x ^ (m + 1 - 1 - i) ≤ y ^ (m + 1 - 1 - i) :=
      pow_le_pow_left₀ hx hxy _
    have h2 : y ^ (m + 1 - 1 - i) = y ^ (m - i) := by
      rw [show m + 1 - 1 - i = m - i by omega]
    rw [h2] at h1
    calc y ^ i * x ^ (m - i) ≤ y ^ i * y ^ (m - i) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (le_trans hx hxy) _)
      _ = y ^ m := by
          rw [← pow_add]
          congr 1
          omega
  have hsum_lo : ((m : ℝ) + 1) * x ^ m
      ≤ ∑ i ∈ Finset.range (m + 1), y ^ i * x ^ (m + 1 - 1 - i) := by
    have h := Finset.sum_le_sum hterm_lo
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    exact h
  have hsum_hi : ∑ i ∈ Finset.range (m + 1), y ^ i * x ^ (m + 1 - 1 - i)
      ≤ ((m : ℝ) + 1) * y ^ m := by
    have h := Finset.sum_le_sum hterm_hi
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    exact h
  have hδ : (0 : ℝ) ≤ y - x := sub_nonneg.mpr hxy
  constructor
  · calc ((m : ℝ) + 1) * x ^ m * (y - x)
        ≤ (∑ i ∈ Finset.range (m + 1), y ^ i * x ^ (m + 1 - 1 - i)) * (y - x) :=
          mul_le_mul_of_nonneg_right hsum_lo hδ
      _ = y ^ (m + 1) - x ^ (m + 1) := hgeom
  · calc y ^ (m + 1) - x ^ (m + 1)
        = (∑ i ∈ Finset.range (m + 1), y ^ i * x ^ (m + 1 - 1 - i)) * (y - x) :=
          hgeom.symm
      _ ≤ ((m : ℝ) + 1) * y ^ m * (y - x) :=
          mul_le_mul_of_nonneg_right hsum_hi hδ

theorem sum_Icc_one_eq_sum_range_aux (f : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, f j = ∑ i ∈ Finset.range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ N + 1 by omega), ih,
      Finset.sum_range_succ]

theorem sum_Icc_two_eq_sum_range_aux (f : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Icc 2 N, f j = ∑ i ∈ Finset.range (N - 1), f (i + 2) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN0 : N = 0
    · subst hN0
      simp
    · have hN1 : 1 ≤ N := by omega
      have ih' := ih hN1
      have htop := Finset.sum_Icc_succ_top (show (2 : ℕ) ≤ N + 1 by omega) (f := f)
      have hrw : (N + 1 - 1) = N := by omega
      rw [htop, ih', hrw]
      have hN' : N = (N - 1) + 1 := by omega
      conv_rhs => rw [hN']
      rw [Finset.sum_range_succ, show (N - 1) + 2 = N + 1 by omega]

theorem sum_inv_mul_succ_aux (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) + 1))
      = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have htop := Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ N + 1 by omega)
      (f := fun j => (1 : ℝ) / ((j : ℝ) * ((j : ℝ) + 1)))
    rw [htop, ih]
    have hN1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hN1]
    have hp1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hp2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    field_simp
    ring

theorem sum_inv_mul_pred_aux {N : ℕ} (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Icc 2 N, (1 : ℝ) / (((j : ℝ) - 1) * (j : ℝ))
      = 1 - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN0 : N = 0
    · subst hN0
      simp
    · have hN1 : 1 ≤ N := by omega
      have ih' := ih hN1
      have htop := Finset.sum_Icc_succ_top (show (2 : ℕ) ≤ N + 1 by omega)
        (f := fun j => (1 : ℝ) / (((j : ℝ) - 1) * (j : ℝ)))
      rw [htop, ih']
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hp1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hsub : ((N : ℝ) + 1) - 1 = (N : ℝ) := by ring
      rw [hsub]
      field_simp
      ring

theorem log_succ_sub_log_aux {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)
      = Real.log (1 + 1 / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast, ← Real.log_div (by simp [hk1]) hk0]
  congr 1
  rw [add_div, div_self hk0]

theorem harmLogPow_bound_of_two_le_aux (m : ℕ) {T : ℕ} (hT : 2 ≤ T) :
    abs (harmLogPow_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ 2 * (Real.log (T : ℝ)) ^ m := by
  classical
  set a : ℕ → ℝ := fun j => (Real.log (j : ℝ)) ^ m with ha
  have hlogT_nn : (0 : ℝ) ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  have hpowT_nn : (0 : ℝ) ≤ (Real.log (T : ℝ)) ^ m := pow_nonneg hlogT_nn m
  have ha_le : ∀ j ∈ Finset.Icc 1 T, a j ≤ (Real.log (T : ℝ)) ^ m := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hjT : (j : ℝ) ≤ (T : ℝ) := by exact_mod_cast hj.2
    have hnn : (0 : ℝ) ≤ Real.log (j : ℝ) := Real.log_nonneg hj1
    exact pow_le_pow_left₀ hnn (Real.log_le_log (by exact_mod_cast (by omega : 0 < j)) hjT) m
  have ha_nn : ∀ j ∈ Finset.Icc 1 T, (0 : ℝ) ≤ a j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    exact pow_nonneg (Real.log_nonneg hj1) m
  -- Telescoping of the main power.
  have htele : (Real.log (T : ℝ)) ^ (m + 1)
      = ∑ k ∈ Finset.range T,
        ((Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log (k : ℝ)) ^ (m + 1)) := by
    have h := Finset.sum_range_sub (fun k => (Real.log (k : ℝ)) ^ (m + 1)) T
    rw [h]
    simp [Real.log_zero, zero_pow (Nat.succ_ne_zero m)]
  -- Peel off k = 0 (its difference is 0).
  have hpeel : ∑ k ∈ Finset.range T,
        ((Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log (k : ℝ)) ^ (m + 1))
      = ∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)) := by
    have h := Finset.sum_range_succ'
      (fun k => (Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log (k : ℝ)) ^ (m + 1))
      (T - 1)
    rw [show T - 1 + 1 = T by omega] at h
    rw [h]
    simp [Real.log_one, Real.log_zero, zero_pow (Nat.succ_ne_zero m)]
  rw [htele, hpeel]
  -- Per-term sandwich for k = i+1 ≥ 1.
  have hterm : ∀ i ∈ Finset.range (T - 1),
      ((m : ℝ) + 1) * a (i + 1) / (((i + 1 : ℕ) : ℝ) + 1)
        ≤ (Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)
        ∧ (Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)
          ≤ ((m : ℝ) + 1) * a (i + 2) / ((i + 1 : ℕ) : ℝ) := by
    intro i _
    set k := i + 1 with hkdef
    have hk1 : 1 ≤ k := by omega
    have hx : (0 : ℝ) ≤ Real.log (k : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hk1)
    have hxy : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < k))
      have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [this]
      linarith
    obtain ⟨hlo, hhi⟩ := pow_succ_sub_pow_sandwich_aux hx hxy m
    have hδ : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)
        = Real.log (1 + 1 / (k : ℝ)) := log_succ_sub_log_aux hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hδlo : 1 / ((k : ℝ) + 1) ≤ Real.log (1 + 1 / (k : ℝ)) :=
      log_one_add_inv_ge_aux hkpos
    have hδhi : Real.log (1 + 1 / (k : ℝ)) ≤ 1 / (k : ℝ) :=
      log_one_add_inv_le_aux hkpos
    have hδnn : (0 : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      rw [hδ]
      apply Real.log_nonneg
      have h1k : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      linarith
    have hcoef_nn : (0 : ℝ) ≤ ((m : ℝ) + 1) * a k :=
      mul_nonneg (by positivity) (by
        have : (0 : ℝ) ≤ a k := pow_nonneg hx m
        exact this)
    have hcast2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    constructor
    · have h1 : ((m : ℝ) + 1) * a k * (1 / ((k : ℝ) + 1))
          ≤ ((m : ℝ) + 1) * a k
            * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (by rw [hδ]; exact hδlo) hcoef_nn
      have h2 : ((m : ℝ) + 1) * a k
            * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ))
          ≤ (Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log (k : ℝ)) ^ (m + 1) :=
        hlo
      have h3 : ((m : ℝ) + 1) * a k / (((i + 1 : ℕ) : ℝ) + 1)
          = ((m : ℝ) + 1) * a k * (1 / ((k : ℝ) + 1)) := by
        have hcast : ((i + 1 : ℕ) : ℝ) = (k : ℝ) := by rw [hkdef]
        rw [hcast, div_eq_mul_one_div]
      rw [h3]
      exact le_trans h1 h2
    · have hcoef : (0 : ℝ) ≤ ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m := by
        positivity
      have hstep : ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m
            * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ))
          ≤ ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m * (1 / (k : ℝ)) := by
        rw [hδ]
        exact mul_le_mul_of_nonneg_left hδhi hcoef
      have hle : (Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log (k : ℝ)) ^ (m + 1)
          ≤ ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m * (1 / (k : ℝ)) :=
        le_trans hhi hstep
      have hconv : ((m : ℝ) + 1) * a (i + 2) / ((i + 1 : ℕ) : ℝ)
          = ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m * (1 / (k : ℝ)) := by
        have h1 : a (i + 2) = (Real.log ((k + 1 : ℕ) : ℝ)) ^ m := by
          have h2 : i + 2 = k + 1 := by omega
          rw [h2]
        have h3 : ((i + 1 : ℕ) : ℝ) = (k : ℝ) := by rw [hkdef]
        calc ((m : ℝ) + 1) * a (i + 2) / ((i + 1 : ℕ) : ℝ)
            = ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m / (k : ℝ) := by
              rw [h1, h3]
          _ = ((m : ℝ) + 1) * (Real.log ((k + 1 : ℕ) : ℝ)) ^ m * (1 / (k : ℝ)) := by
              rw [div_eq_mul_one_div]
      rw [hconv]
      exact hle
  -- Sum the sandwich.
  have hsum_lo : ((m : ℝ) + 1)
        * (∑ i ∈ Finset.range (T - 1), a (i + 1) / (((i + 1 : ℕ) : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => by
      rw [← mul_div_assoc]
      exact (hterm i hi).1)
  have hsum_hi : ∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1))
      ≤ ((m : ℝ) + 1)
        * (∑ i ∈ Finset.range (T - 1), a (i + 2) / ((i + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => by
      rw [← mul_div_assoc]
      exact (hterm i hi).2)
  -- Identify the two comparison sums with Icc sums.
  have hlow_id : (∑ i ∈ Finset.range (T - 1), a (i + 1) / (((i + 1 : ℕ) : ℝ) + 1))
      = ∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) + 1) := by
    have h := sum_Icc_one_eq_sum_range_aux (fun j => a j / ((j : ℝ) + 1)) (T - 1)
    exact h.symm
  have hup_id : (∑ i ∈ Finset.range (T - 1), a (i + 2) / ((i + 1 : ℕ) : ℝ))
      = ∑ j ∈ Finset.Icc 2 T, a j / ((j : ℝ) - 1) := by
    have h := sum_Icc_two_eq_sum_range_aux (fun j => a j / ((j : ℝ) - 1))
      (show (1 : ℕ) ≤ T by omega)
    have hterm_eq : ∀ i ∈ Finset.range (T - 1),
        a (i + 2) / ((i + 1 : ℕ) : ℝ) = (fun j => a j / ((j : ℝ) - 1)) (i + 2) := by
      intro i _
      have hcast : (((i + 2 : ℕ) : ℝ) - 1) = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
      show a (i + 2) / ((i + 1 : ℕ) : ℝ) = a (i + 2) / (((i + 2 : ℕ) : ℝ) - 1)
      rw [hcast]
    rw [h]
    exact Finset.sum_congr rfl hterm_eq
  rw [hlow_id] at hsum_lo
  rw [hup_id] at hsum_hi
  -- Compare the Icc comparison sums with harmLogPow_aux.
  have hsplit : harmLogPow_aux m T
      = (∑ j ∈ Finset.Icc 1 (T - 1), a j / (j : ℝ)) + a T / (T : ℝ) := by
    have h := Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ T - 1 + 1 by omega)
      (f := fun j => a j / (j : ℝ))
    rw [show T - 1 + 1 = T by omega] at h
    unfold harmLogPow_aux
    exact h
  have hlow_cmp : (∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) + 1))
      ≥ (∑ j ∈ Finset.Icc 1 (T - 1), a j / (j : ℝ))
        - (Real.log (T : ℝ)) ^ m := by
    have hdiff : (∑ j ∈ Finset.Icc 1 (T - 1), a j / (j : ℝ))
          - (∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) + 1))
        = ∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) * ((j : ℝ) + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hbound : ∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) * ((j : ℝ) + 1))
        ≤ (Real.log (T : ℝ)) ^ m := by
      calc ∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) * ((j : ℝ) + 1))
          ≤ ∑ j ∈ Finset.Icc 1 (T - 1),
              (Real.log (T : ℝ)) ^ m * (1 / ((j : ℝ) * ((j : ℝ) + 1))) := by
            apply Finset.sum_le_sum
            intro j hj
            have haj := ha_le j (Finset.Icc_subset_Icc le_rfl (by omega : T - 1 ≤ T) hj)
            have hnn : (0 : ℝ) ≤ 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
              have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
                exact_mod_cast (Finset.mem_Icc.mp hj).1
              exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right haj hnn
        _ = (Real.log (T : ℝ)) ^ m
            * (∑ j ∈ Finset.Icc 1 (T - 1), 1 / ((j : ℝ) * ((j : ℝ) + 1))) := by
            rw [Finset.mul_sum]
        _ = (Real.log (T : ℝ)) ^ m * (1 - 1 / (((T - 1 : ℕ) : ℝ) + 1)) := by
            rw [sum_inv_mul_succ_aux]
        _ ≤ (Real.log (T : ℝ)) ^ m * 1 := by
            apply mul_le_mul_of_nonneg_left _ hpowT_nn
            have hpos : (0 : ℝ) ≤ 1 / (((T - 1 : ℕ) : ℝ) + 1) := by positivity
            linarith
        _ = (Real.log (T : ℝ)) ^ m := mul_one _
    linarith
  have hup_cmp : (∑ j ∈ Finset.Icc 2 T, a j / ((j : ℝ) - 1))
      ≤ harmLogPow_aux m T + (Real.log (T : ℝ)) ^ m := by
    have hdiff : (∑ j ∈ Finset.Icc 2 T, a j / ((j : ℝ) - 1))
          - (∑ j ∈ Finset.Icc 2 T, a j / (j : ℝ))
        = ∑ j ∈ Finset.Icc 2 T, a j / (((j : ℝ) - 1) * (j : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hj1 : ((j : ℝ) - 1) ≠ 0 := by
        have h2j : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        have hpos : (0 : ℝ) < (j : ℝ) - 1 := by linarith
        exact hpos.ne'
      field_simp
      ring
    have hbound : ∑ j ∈ Finset.Icc 2 T, a j / (((j : ℝ) - 1) * (j : ℝ))
        ≤ (Real.log (T : ℝ)) ^ m := by
      calc ∑ j ∈ Finset.Icc 2 T, a j / (((j : ℝ) - 1) * (j : ℝ))
          ≤ ∑ j ∈ Finset.Icc 2 T,
              (Real.log (T : ℝ)) ^ m * (1 / (((j : ℝ) - 1) * (j : ℝ))) := by
            apply Finset.sum_le_sum
            intro j hj
            have haj := ha_le j (Finset.Icc_subset_Icc (by omega : 1 ≤ 2) le_rfl hj)
            have hnn : (0 : ℝ) ≤ 1 / (((j : ℝ) - 1) * (j : ℝ)) := by
              have hj2 : (2 : ℝ) ≤ (j : ℝ) := by
                exact_mod_cast (Finset.mem_Icc.mp hj).1
              exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith))
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right haj hnn
        _ = (Real.log (T : ℝ)) ^ m
            * (∑ j ∈ Finset.Icc 2 T, 1 / (((j : ℝ) - 1) * (j : ℝ))) := by
            rw [Finset.mul_sum]
        _ = (Real.log (T : ℝ)) ^ m * (1 - 1 / (T : ℝ)) := by
            rw [sum_inv_mul_pred_aux (show (1 : ℕ) ≤ T by omega)]
        _ ≤ (Real.log (T : ℝ)) ^ m * 1 := by
            apply mul_le_mul_of_nonneg_left _ hpowT_nn
            have hpos : (0 : ℝ) ≤ 1 / (T : ℝ) := by positivity
            linarith
        _ = (Real.log (T : ℝ)) ^ m := mul_one _
    have hsub : (∑ j ∈ Finset.Icc 2 T, a j / (j : ℝ)) ≤ harmLogPow_aux m T := by
      unfold harmLogPow_aux
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc (by omega : 1 ≤ 2) le_rfl
      · intro j hj _
        rw [Finset.mem_Icc] at hj
        have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        exact div_nonneg (pow_nonneg (Real.log_nonneg hj1) m) (by positivity)
    linarith
  -- Assemble: (m+1) * (H - 2 L^m) ≤ Pow ≤ (m+1) * (H + L^m).
  have haT_div : a T / (T : ℝ) ≤ (Real.log (T : ℝ)) ^ m := by
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
    have : a T = (Real.log (T : ℝ)) ^ m := rfl
    rw [this]
    exact div_le_self hpowT_nn hT1
  have hlow_main : ((m : ℝ) + 1) * (harmLogPow_aux m T - 2 * (Real.log (T : ℝ)) ^ m)
      ≤ ∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)) := by
    have h1 : ((m : ℝ) + 1) * (harmLogPow_aux m T - 2 * (Real.log (T : ℝ)) ^ m)
        ≤ ((m : ℝ) + 1) * (∑ j ∈ Finset.Icc 1 (T - 1), a j / ((j : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h2 : (∑ j ∈ Finset.Icc 1 (T - 1), a j / (j : ℝ))
          ≤ harmLogPow_aux m T := by
        rw [hsplit]
        have : (0 : ℝ) ≤ a T / (T : ℝ) := by
          exact div_nonneg hpowT_nn (by positivity)
        linarith
      linarith [hlow_cmp, h2, haT_div]
    exact le_trans h1 hsum_lo
  have hup_main : ∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1))
      ≤ ((m : ℝ) + 1) * (harmLogPow_aux m T + (Real.log (T : ℝ)) ^ m) := by
    have h1 : ((m : ℝ) + 1) * (∑ j ∈ Finset.Icc 2 T, a j / ((j : ℝ) - 1))
        ≤ ((m : ℝ) + 1) * (harmLogPow_aux m T + (Real.log (T : ℝ)) ^ m) :=
      mul_le_mul_of_nonneg_left hup_cmp (by positivity)
    exact le_trans hsum_hi h1
  -- Convert to the abs bound.
  have hc : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hdiv_lo : harmLogPow_aux m T - 2 * (Real.log (T : ℝ)) ^ m
      ≤ (∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1))) / ((m : ℝ) + 1) := by
    apply (le_div_iff₀ hc).mpr
    rw [mul_comm]
    exact hlow_main
  have hdiv_hi : (∑ i ∈ Finset.range (T - 1),
        ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
          - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1))) / ((m : ℝ) + 1)
      ≤ harmLogPow_aux m T + (Real.log (T : ℝ)) ^ m := by
    apply (div_le_iff₀ hc).mpr
    rw [mul_comm]
    exact hup_main
  rw [abs_le]
  constructor
  · have hsum_eq : (∑ i ∈ Finset.range (T - 1),
          ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)))
        = (Real.log (T : ℝ)) ^ (m + 1) := by
      rw [← hpeel, ← htele]
    have h1 : (∑ i ∈ Finset.range (T - 1),
          ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1))) / ((m : ℝ) + 1)
        = (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) := by
      rw [hsum_eq]
    rw [h1] at hdiv_hi
    linarith [hdiv_hi, hpowT_nn]
  · have hsum_eq : (∑ i ∈ Finset.range (T - 1),
          ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1)))
        = (Real.log (T : ℝ)) ^ (m + 1) := by
      rw [← hpeel, ← htele]
    have h1 : (∑ i ∈ Finset.range (T - 1),
          ((Real.log ((i + 1 + 1 : ℕ) : ℝ)) ^ (m + 1)
            - (Real.log ((i + 1 : ℕ) : ℝ)) ^ (m + 1))) / ((m : ℝ) + 1)
        = (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1) := by
      rw [hsum_eq]
    rw [h1] at hdiv_lo
    linarith [hdiv_lo, hpowT_nn]

theorem harmLogPow_bound_of_small_aux (m : ℕ) {T : ℕ} (hT : T ≤ 1) :
    abs (harmLogPow_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ 2 * (Real.log (T : ℝ)) ^ m := by
  interval_cases T
  · simp [harmLogPow_aux, Real.log_zero, zero_pow (Nat.succ_ne_zero m)]
  · have hsum : harmLogPow_aux m 1 = (Real.log (1 : ℝ)) ^ m / (1 : ℝ) := by
      unfold harmLogPow_aux
      rw [Finset.Icc_self]
      simp
    rw [hsum]
    simp only [Nat.cast_one, Real.log_one, div_one]
    by_cases hm : m = 0
    · subst hm
      simp
    · have h0 : (0 : ℝ) ^ m = 0 := zero_pow (by omega : m ≠ 0)
      have h1 : (0 : ℝ) ^ (m + 1) = 0 := zero_pow (Nat.succ_ne_zero m)
      rw [h0, h1]
      simp

theorem harmLogPow_bound_aux (m : ℕ) (T : ℕ) :
    abs (harmLogPow_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ 2 * (Real.log (T : ℝ)) ^ m := by
  by_cases hT : 2 ≤ T
  · exact harmLogPow_bound_of_two_le_aux m hT
  · exact harmLogPow_bound_of_small_aux m (by omega)

def truncSet_aux (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (∏ p ∈ S, p ^ 2 + 1)).filter (fun d =>
    1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2)

theorem truncSet_bound_aux {S : Finset ℕ} {d : ℕ}
    (hd1 : 1 ≤ d) (hd : ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    d ≤ ∏ p ∈ S, p ^ 2 := by
  have hd0 : d ≠ 0 := by omega
  have h := Nat.prod_factorization_pow_eq_self hd0
  rw [← h]
  show (∏ p ∈ d.factorization.support, p ^ d.factorization p) ≤ _
  rw [Nat.support_factorization]
  calc (∏ p ∈ d.primeFactors, p ^ d.factorization p)
      ≤ ∏ p ∈ d.primeFactors, p ^ 2 := by
        apply Finset.prod_le_prod'
        intro p hp
        have hp2 : 2 ≤ p := hS p (hd p hp).1
        exact pow_le_pow_right₀ (by omega) (hd p hp).2
    _ ≤ ∏ p ∈ S, p ^ 2 := by
        apply Finset.prod_le_prod_of_subset_of_one_le'
        · intro p hp
          exact (hd p hp).1
        · intro p hpS _
          have hp2 : 2 ≤ p := hS p hpS
          exact one_le_pow₀ (by omega)

theorem mem_truncSet_aux {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {d : ℕ} :
    d ∈ truncSet_aux S ↔ 1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2 := by
  constructor
  · intro hd
    simp only [truncSet_aux, Finset.mem_filter] at hd
    exact hd.2
  · intro ⟨hd1, hd⟩
    simp only [truncSet_aux, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hd1, hd⟩
    have hb := truncSet_bound_aux hd1 hd hS
    omega

theorem not_mem_primeFactors_of_mem_truncSet_aux {S : Finset ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p) {d₀ : ℕ} (hd₀ : d₀ ∈ truncSet_aux S) {q : ℕ} (hqS : q ∉ S) :
    q ∉ d₀.primeFactors := by
  intro hqmem
  exact hqS (((mem_truncSet_aux hS).mp hd₀).2 q hqmem).1

theorem factorization_eq_zero_of_mem_truncSet_aux {S : Finset ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p) {d₀ : ℕ} (hd₀ : d₀ ∈ truncSet_aux S) {q : ℕ}
    (hq : q.Prime) (hqS : q ∉ S) :
    d₀.factorization q = 0 := by
  have hd0 : d₀ ≠ 0 := by
    have h1 := ((mem_truncSet_aux hS).mp hd₀).1
    omega
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdvd
  exact not_mem_primeFactors_of_mem_truncSet_aux hS hd₀ hqS
    (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd0⟩)

theorem factorization_mul_pow_aux {d₀ q j : ℕ} (hq : q.Prime)
    (hd₀ : d₀ ≠ 0) (hqd : q ∉ d₀.primeFactors) :
    (d₀ * q ^ j).factorization q = j := by
  have hqdvd : ¬ q ∣ d₀ := by
    intro hdvd
    exact hqd (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd₀⟩)
  rw [Nat.factorization_mul hd₀ (pow_ne_zero j hq.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hqdvd, zero_add]
  simp [hq.factorization_pow]

theorem truncSet_image_insert_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) :
    truncSet_aux (insert q S)
      = (truncSet_aux S ×ˢ Finset.range 3).image (fun x : ℕ × ℕ => x.1 * q ^ x.2) := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hSq : ∀ p ∈ insert q S, 2 ≤ p := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hq.two_le
    · exact hS2 p hp
  ext d
  constructor
  · intro hd
    obtain ⟨hd1, hdcond⟩ := (mem_truncSet_aux hSq).mp hd
    have hd0 : d ≠ 0 := by omega
    set v := d.factorization q with hv
    have hv3 : v < 3 := by
      by_cases hqmem : q ∈ d.primeFactors
      · have hle := (hdcond q hqmem).2
        omega
      · have h0 : d.factorization q = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (by
            intro hdvd
            exact hqmem (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd0⟩))
        omega
    have hdiv : q ^ v ∣ d := Nat.ordProj_dvd d q
    have hd0mem : d / q ^ v ∈ truncSet_aux S := by
      rw [mem_truncSet_aux hS2]
      refine ⟨?_, ?_⟩
      · by_contra hcon
        have h0' : d / q ^ v = 0 := by
          have hlt := Nat.not_le.mp hcon
          exact Nat.lt_one_iff.mp hlt
        have hmul := Nat.div_mul_cancel hdiv
        rw [h0', zero_mul] at hmul
        omega
      · intro p hp
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hpdvd : p ∣ d / q ^ v := (Nat.mem_primeFactors.mp hp).2.1
        have hdvd : p ∣ d :=
          dvd_trans hpdvd ⟨q ^ v, (Nat.div_mul_cancel hdiv).symm⟩
        have hpmem : p ∈ d.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, hd0⟩
        have hpq : p ≠ q := by
          intro hpeq
          have hqmem : q ∈ (d / q ^ v).primeFactors := by
            obtain ⟨hprime, hdvd, hd0'⟩ := Nat.mem_primeFactors.mp hp
            exact Nat.mem_primeFactors.mpr ⟨hpeq ▸ hprime, hpeq ▸ hdvd, hd0'⟩
          have hfac0 : (d / q ^ v).factorization q = 0 := by
            rw [Nat.factorization_div hdiv, Finsupp.tsub_apply]
            have hqv : (q ^ v).factorization q = v := by simp [hq.factorization_pow]
            rw [hqv, tsub_self]
          have hne : (d / q ^ v).factorization q ≠ 0 := by
            have hmem : q ∈ (d / q ^ v).factorization.support := by
              rw [Nat.support_factorization]
              exact hqmem
            exact Finsupp.mem_support_iff.mp hmem
          exact hne hfac0
        refine ⟨?_, ?_⟩
        · have hmem := (hdcond p hpmem).1
          simp only [Finset.mem_insert] at hmem
          rcases hmem with h | h
          · exact absurd h hpq
          · exact h
        · have hfac : (d / q ^ v).factorization p = d.factorization p := by
            rw [Nat.factorization_div hdiv, Finsupp.tsub_apply]
            have hqfac : (q ^ v).factorization p = 0 := by
              apply Nat.factorization_eq_zero_of_not_dvd
              intro hdvdp
              have hpqdvd : p ∣ q := hpprime.dvd_of_dvd_pow hdvdp
              exact hpq ((Nat.prime_dvd_prime_iff_eq hpprime hq).mp hpqdvd)
            rw [hqfac, tsub_zero]
          rw [hfac]
          exact (hdcond p hpmem).2
    rw [Finset.mem_image]
    refine ⟨(d / q ^ v, v), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨hd0mem, Finset.mem_range.mpr hv3⟩
    · exact Nat.div_mul_cancel hdiv
  · intro hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨d₀, j⟩, hmem, hmap⟩ := hd
    rw [Finset.mem_product] at hmem
    obtain ⟨hd₀, hj⟩ := hmem
    rw [Finset.mem_range] at hj
    have hmap' : d₀ * q ^ j = d := hmap
    rw [← hmap']
    rw [mem_truncSet_aux hSq]
    have hd01 := ((mem_truncSet_aux hS2).mp hd₀).1
    have hd00 : d₀ ≠ 0 := by omega
    have hqj0 : q ^ j ≠ 0 := pow_ne_zero j hq.ne_zero
    have hd₀cond := ((mem_truncSet_aux hS2).mp hd₀).2
    have hqnot : q ∉ d₀.primeFactors :=
      not_mem_primeFactors_of_mem_truncSet_aux hS2 hd₀ hqS
    have hfacq0 : d₀.factorization q = 0 :=
      factorization_eq_zero_of_mem_truncSet_aux hS2 hd₀ hq hqS
    refine ⟨?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hqj0)
    · intro p hp
      rw [Nat.primeFactors_mul hd00 hqj0, Finset.mem_union] at hp
      rcases hp with hp | hp
      · have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        refine ⟨?_, ?_⟩
        · simp only [Finset.mem_insert]
          exact Or.inr (hd₀cond p hp).1
        · rw [Nat.factorization_mul hd00 hqj0, Finsupp.add_apply]
          have hqfac : (q ^ j).factorization p = 0 := by
            apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvdp
            have hpqdvd : p ∣ q := hpprime.dvd_of_dvd_pow hdvdp
            have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hpprime hq).mp hpqdvd
            exact hqnot (hpeq ▸ hp)
          rw [hqfac, add_zero]
          exact (hd₀cond p hp).2
      · have hj0 : j ≠ 0 := by
          intro hj0
          subst hj0
          simp at hp
        have hpq : p = q := by
          have hpf : (q ^ j).primeFactors = {q} :=
            Nat.primeFactors_prime_pow hj0 hq
          rw [hpf, Finset.mem_singleton] at hp
          exact hp
        subst hpq
        refine ⟨?_, ?_⟩
        · exact Finset.mem_insert_self p S
        · rw [Nat.factorization_mul hd00 hqj0, Finsupp.add_apply, hfacq0, zero_add]
          have hqj : (p ^ j).factorization p = j := by simp [hq.factorization_pow]
          rw [hqj]
          omega

theorem sum_truncSet_insert_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) (F : ℕ → ℝ) :
    ∑ d ∈ truncSet_aux (insert q S), F d
      = ∑ d₀ ∈ truncSet_aux S, ∑ j ∈ Finset.range 3, F (d₀ * q ^ j) := by
  rw [truncSet_image_insert_aux hS hq hqS, Finset.sum_image]
  · rw [Finset.sum_product]
  · intro x hx y hy hxy
    have hxy' : x.1 * q ^ x.2 = y.1 * q ^ y.2 := hxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [Finset.mem_range] at hx2 hy2
    have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
    have hx0 : x.1 ≠ 0 := by
      have h1 := ((mem_truncSet_aux hS2).mp hx1).1
      omega
    have hy0 : y.1 ≠ 0 := by
      have h1 := ((mem_truncSet_aux hS2).mp hy1).1
      omega
    have hfac : x.2 = y.2 := by
      have e1 : (x.1 * q ^ x.2).factorization q = x.2 :=
        factorization_mul_pow_aux hq hx0 (by
          intro hdvd
          exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hx1 hqS hdvd)
      have e2 : (y.1 * q ^ y.2).factorization q = y.2 :=
        factorization_mul_pow_aux hq hy0 (by
          intro hdvd
          exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hy1 hqS hdvd)
      rw [hxy'] at e1
      exact e1.symm.trans e2
    have h1 : x.1 = y.1 := by
      rw [hfac] at hxy'
      exact mul_right_cancel₀ (pow_ne_zero y.2 hq.ne_zero) hxy'
    exact Prod.ext h1 hfac

/-- Euler-product formula for truncated sums of a multiplicative weight. -/
theorem sum_truncSet_eq_prod_aux (w : ℕ → ℝ) (hw1 : w 1 = 1)
    (hwmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → w (m * n) = w m * w n) :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    ∑ d ∈ truncSet_aux S, w d = ∏ p ∈ S, (∑ j ∈ Finset.range 3, w (p ^ j)) := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro _
    have hset : truncSet_aux (∅ : Finset ℕ) = {1} := by
      ext d
      simp only [truncSet_aux, Finset.mem_filter, Finset.mem_range, Finset.prod_empty,
        Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, -⟩
        omega
      · intro hd
        subst hd
        refine ⟨by omega, le_refl 1, ?_⟩
        intro p hp
        rw [Nat.primeFactors_one] at hp
        exact absurd hp (Finset.notMem_empty p)
    rw [hset]
    simp [hw1]
  | @insert q S hqS ih =>
    intro hS
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hq : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS' p hp).two_le
    rw [sum_truncSet_insert_aux hS' hq hqS, Finset.prod_insert hqS]
    trans (∑ d₀ ∈ truncSet_aux S, w d₀ * (∑ j ∈ Finset.range 3, w (q ^ j)))
    · apply Finset.sum_congr rfl
      intro d₀ hd₀
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hd00 : d₀ ≠ 0 := by
        have h1 := ((mem_truncSet_aux hS2).mp hd₀).1
        omega
      have hnot : ¬ q ∣ d₀ := by
        intro hdvd
        exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hd₀ hqS
          (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd00⟩)
      have hcop : Nat.Coprime d₀ (q ^ j) :=
        ((hq.coprime_iff_not_dvd.mpr hnot).symm).pow_right j
      exact hwmul hd00 (pow_ne_zero j hq.ne_zero) hcop
    · rw [← Finset.sum_mul, ih hS']
      exact mul_comm _ _

/-! ### The weight `w d = |c d| / d` and the bound `∑ w ≤ e²` -/

theorem sum_Icc_eq_filter_truncSet_aux {T : ℕ} {S : Finset ℕ}
    (hS2 : ∀ p ∈ S, 2 ≤ p)
    (f : ℕ → ℝ) (hf : ∀ d ∈ Finset.Icc 1 T, d ∉ truncSet_aux S → f d = 0) :
    (∑ d ∈ Finset.Icc 1 T, f d)
      = ∑ d ∈ (truncSet_aux S).filter (fun d => d ≤ T), f d := by
  have hset : (Finset.Icc 1 T).filter (fun d => d ∈ truncSet_aux S)
      = (truncSet_aux S).filter (fun d => d ≤ T) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd1, hdT⟩, hdS⟩
      exact ⟨hdS, hdT⟩
    · rintro ⟨hdS, hdT⟩
      have hd1 : 1 ≤ d := ((mem_truncSet_aux hS2).mp hdS).1
      exact ⟨⟨hd1, hdT⟩, hdS⟩
  have hvan : (∑ d ∈ Finset.Icc 1 T, f d)
      = ∑ d ∈ (Finset.Icc 1 T).filter (fun d => d ∈ truncSet_aux S), f d := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 T)
      (fun d => d ∈ truncSet_aux S) f]
    have hz : ∑ d ∈ (Finset.Icc 1 T).filter (fun d => ¬ d ∈ truncSet_aux S), f d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact hf d (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
    rw [hz, add_zero]
  rw [hvan, hset]

/-- The swap identity: `S₀(T)` as a sum of harmonic sums weighted by `c(d)/d`. -/

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def twistedWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  (∏ p ∈ n.primeFactors, ((localGoodChoiceFinset h i p hd he).card : ℝ))
    / ((Nat.totient n : ℕ) : ℝ)

noncomputable def twistedMuSqSum {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (m M Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n M),
    (ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n
      * (Real.log (n : ℝ)) ^ m

noncomputable def twistedAbsWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  abs ((ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n)

/-- The twisted weight at `1` is `1`. -/
theorem twistedWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedWeight h i hd he 1 = 1 := by
  unfold twistedWeight
  simp

/-- The twisted weight is multiplicative on coprime pairs. -/
theorem twistedWeight_mul_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    twistedWeight h i hd he (m * n)
      = twistedWeight h i hd he m * twistedWeight h i hd he n := by
  unfold twistedWeight
  have hdisj : Disjoint m.primeFactors n.primeFactors := hcop.disjoint_primeFactors
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union hdisj, Nat.totient_mul hcop,
    Nat.cast_mul, div_mul_div_comm]

/-- The twisted weight at a prime: `c_p / (p - 1)`. -/
theorem twistedWeight_prime_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedWeight h i hd he p
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  unfold twistedWeight
  have hcast : ((Nat.totient p : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    push_cast
    ring
  rw [hp.primeFactors, Finset.prod_singleton, hcast]

/-- Nonnegativity of the absolute twisted weight. -/
theorem twistedAbsWeight_nonneg_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) :
    (0 : ℝ) ≤ twistedAbsWeight h i hd he n := by
  unfold twistedAbsWeight
  exact abs_nonneg _

/-- The absolute twisted weight at `1` is `1`. -/
theorem twistedAbsWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedAbsWeight h i hd he 1 = 1 := by
  unfold twistedAbsWeight
  rw [twistedWeight_one_aux, ArithmeticFunction.moebius_apply_one]
  simp

/-- The absolute twisted weight is multiplicative on coprime pairs. -/
theorem twistedAbsWeight_mul_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    twistedAbsWeight h i hd he (m * n)
      = twistedAbsWeight h i hd he m * twistedAbsWeight h i hd he n := by
  unfold twistedAbsWeight
  have hmu : ArithmeticFunction.moebius (m * n)
      = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hmuR : ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ)
        * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
    rw [hmu]
    push_cast
    ring
  rw [hmuR, twistedWeight_mul_aux h i hd he hm hn hcop]
  simp only [abs_mul]
  ring

/-- The absolute twisted weight at a prime: `c_p / (p - 1)`. -/
theorem twistedAbsWeight_prime_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedAbsWeight h i hd he p
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  unfold twistedAbsWeight
  rw [twistedWeight_prime_aux h i hd he hp, ArithmeticFunction.moebius_apply_prime hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hC : (0 : ℝ) ≤ ((localGoodChoiceFinset h i p hd he).card : ℝ) :=
    Nat.cast_nonneg _
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hcast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_cast
  rw [hcast]
  rw [abs_mul, abs_neg, abs_one, one_mul,
    abs_of_nonneg (div_nonneg hC (le_of_lt hden))]

/-- The absolute twisted weight at `p²` is `0` (Möbius vanishes). -/
theorem twistedAbsWeight_prime_pow_two_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedAbsWeight h i hd he (p ^ 2) = 0 := by
  unfold twistedAbsWeight
  have hmu : ArithmeticFunction.moebius (p ^ 2) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num : (2 : ℕ) ≠ 0)]
    simp
  have hmuR : ((ArithmeticFunction.moebius (p ^ 2) : ℤ) : ℝ) = 0 := by
    rw [hmu]
    simp
  rw [hmuR]
  simp

/-! ### The uniform local-count bound -/

/-- The local count is at most `(k+1)²`: the local choice finset
    is a subfinset of `univ` over `Option (Fin k) × Option (Fin k)`. -/
theorem localGoodChoice_card_le_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    ((localGoodChoiceFinset h i p hd he).card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
  have hcard : (localGoodChoiceFinset h i p hd he).card ≤ (k + 1) * (k + 1) := by
    calc (localGoodChoiceFinset h i p hd he).card
        ≤ Finset.univ.card := Finset.card_le_univ _
      _ = (k + 1) * (k + 1) := by
          simp [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  have hcast : (((k + 1) * (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) ^ 2 := by
    push_cast
    ring
  calc ((localGoodChoiceFinset h i p hd he).card : ℝ)
      ≤ (((k + 1) * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((k : ℝ) + 1) ^ 2 := hcast

/-! ### Truncated Euler product for the absolute twisted weight -/

/-- Local sums at prime powers: `1 + c_p/(p-1)`. -/
theorem sum_twistedAbsWeight_prime_pow_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    ∑ j ∈ Finset.range 3, twistedAbsWeight h i hd he (p ^ j)
      = 1 + ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  have e0 : twistedAbsWeight h i hd he (p ^ 0) = 1 := by
    simp [twistedAbsWeight_one_aux]
  have e1 : twistedAbsWeight h i hd he (p ^ 1)
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
    rw [pow_one]
    exact twistedAbsWeight_prime_aux h i hd he hp
  have e2 : twistedAbsWeight h i hd he (p ^ 2) = 0 :=
    twistedAbsWeight_prime_pow_two_aux h i hd he hp
  rw [e0, e1, e2]
  ring

/-- TRUNCATED EULER PRODUCT. Over any prime finset `S`, the
    truncated sum of the absolute twisted weight factors exactly
    as the product of the local sums `1 + c_p/(p-1)`. -/
theorem sum_truncSet_twistedAbsWeight_eq_prod_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ truncSet_aux S, twistedAbsWeight h i hd he d
      = ∏ p ∈ S, (1 + ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1)) := by
  rw [sum_truncSet_eq_prod_aux (twistedAbsWeight h i hd he)
    (twistedAbsWeight_one_aux h i hd he)
    (fun hm hn hcop => twistedAbsWeight_mul_aux h i hd he hm hn hcop) S hS]
  apply Finset.prod_congr rfl
  intro p hp
  exact sum_twistedAbsWeight_prime_pow_aux h i hd he (hS p hp)

/-! ### From the truncated product to the range bound -/

/-- A number with nonzero absolute twisted weight lies in the
    truncated set over the primes `≤ T`: nonzero Möbius forces
    squarefreeness, hence exponents `≤ 1 ≤ 2` and prime factors `≤ T`. -/
theorem mem_truncSet_of_twistedAbsWeight_ne_zero_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {T : ℕ} {d : ℕ} (hdT : d ∈ Finset.Icc 1 T)
    (hw : twistedAbsWeight h i hd he d ≠ 0) :
    d ∈ truncSet_aux ((Finset.range (T + 1)).filter (fun p => p.Prime)) := by
  set S := (Finset.range (T + 1)).filter (fun p => p.Prime) with hSdef
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hsq : Squarefree d := by
    by_contra hnsq
    apply hw
    unfold twistedAbsWeight
    have hmu : ArithmeticFunction.moebius d = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    have hmuR : ((ArithmeticFunction.moebius d : ℤ) : ℝ) = 0 := by
      rw [hmu]
      simp
    rw [hmuR]
    simp
  rw [mem_truncSet_aux hS2]
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdT).1
  have hdT' : d ≤ T := (Finset.mem_Icc.mp hdT).2
  refine ⟨hd1, ?_⟩
  intro p hp
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
  have hple : p ≤ d := Nat.le_of_dvd (by omega) hpdvd
  have hpT : p ∈ Finset.range (T + 1) := by
    rw [Finset.mem_range]
    omega
  refine ⟨?_, ?_⟩
  · rw [hSdef, Finset.mem_filter]
    exact ⟨hpT, hpprime⟩
  · have hle := (Nat.squarefree_iff_factorization_le_one (by omega : d ≠ 0)).mp hsq p
    omega

/-- RANGE ABSOLUTE BOUND. For `T ≥ 2`, the absolute twisted sum
    over `n ∈ [1, T]` is at most `exp (2 * (k+1)² * (log T + 2))`.
    The exponent is `2 * (k+1)²` times the harmonic bound, via
    `c_p/(p-1) ≤ 2(k+1)²/p` and `∑_{p ≤ T} 1/p ≤ log T + 2`. -/
theorem twistedAbsWeight_sum_Icc_le_exp_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {T : ℕ} (hT : 2 ≤ T) :
    ∑ n ∈ Finset.Icc 1 T, twistedAbsWeight h i hd he n
      ≤ Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (T : ℝ) + 2)) := by
  set S := (Finset.range (T + 1)).filter (fun p => p.Prime) with hSdef
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hK : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by positivity
  -- Step 1: the Icc sum equals the filtered truncated sum, hence ≤ the full one.
  have hstep1 : ∑ n ∈ Finset.Icc 1 T, twistedAbsWeight h i hd he n
      ≤ ∑ d ∈ truncSet_aux S, twistedAbsWeight h i hd he d := by
    have hIcc : (∑ n ∈ Finset.Icc 1 T, twistedAbsWeight h i hd he n)
        = ∑ d ∈ (truncSet_aux S).filter (fun d => d ≤ T),
            twistedAbsWeight h i hd he d := by
      apply sum_Icc_eq_filter_truncSet_aux hS2 (twistedAbsWeight h i hd he)
      intro d hdIcc hdnot
      by_contra hw
      exact hdnot (mem_truncSet_of_twistedAbsWeight_ne_zero_aux h i hd he hdIcc hw)
    rw [hIcc]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro d _ _
    exact twistedAbsWeight_nonneg_aux h i hd he d
  -- Step 2: the truncated sum is the Euler product.
  have hstep2 : ∑ d ∈ truncSet_aux S, twistedAbsWeight h i hd he d
      = ∏ p ∈ S, (1 + ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1)) :=
    sum_truncSet_twistedAbsWeight_eq_prod_aux h i hd he hS
  -- Step 3: the product is at most exp of the sum of local terms.
  have hstep3 : ∏ p ∈ S, (1 + ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1))
      ≤ Real.exp (∑ p ∈ S, ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
      have hC : (0 : ℝ) ≤ ((localGoodChoiceFinset h i p hd he).card : ℝ) :=
        Nat.cast_nonneg _
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · intro p hp
      rw [add_comm]
      exact Real.add_one_le_exp _
  -- Step 4: the sum of local terms is at most 2 (k+1)² (log T + 2).
  have hstep4 : (∑ p ∈ S, ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1))
      ≤ 2 * ((k : ℝ) + 1) ^ 2 * (Real.log (T : ℝ) + 2) := by
    have hterm : ∀ p ∈ S, ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1) ≤ 2 * ((k : ℝ) + 1) ^ 2 / (p : ℝ) := by
      intro p hp
      have hpprime : p.Prime := hS p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
      have hC : ((localGoodChoiceFinset h i p hd he).card : ℝ)
          ≤ ((k : ℝ) + 1) ^ 2 := localGoodChoice_card_le_aux h i p hd he
      have hCnn : (0 : ℝ) ≤ ((localGoodChoiceFinset h i p hd he).card : ℝ) :=
        Nat.cast_nonneg _
      have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hpos : (0 : ℝ) < (p : ℝ) := by linarith
      have hle : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
      have hone : (1 : ℝ) / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
        have h1 : (1 : ℝ) / ((p : ℝ) - 1) = 2 / (2 * ((p : ℝ) - 1)) := by
          field_simp
        rw [h1]
        exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hpos hle
      calc ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1)
          = ((localGoodChoiceFinset h i p hd he).card : ℝ)
              * (1 / ((p : ℝ) - 1)) := by rw [mul_one_div]
        _ ≤ ((k : ℝ) + 1) ^ 2 * (2 / (p : ℝ)) :=
            mul_le_mul hC hone (by positivity) hK
        _ = 2 * ((k : ℝ) + 1) ^ 2 / (p : ℝ) := by ring
    have hsum1 : (∑ p ∈ S, ((localGoodChoiceFinset h i p hd he).card : ℝ)
            / ((p : ℝ) - 1))
        ≤ ∑ p ∈ S, 2 * ((k : ℝ) + 1) ^ 2 / (p : ℝ) :=
      Finset.sum_le_sum hterm
    have hsum2 : (∑ p ∈ S, 2 * ((k : ℝ) + 1) ^ 2 / (p : ℝ))
        = 2 * ((k : ℝ) + 1) ^ 2 * (∑ p ∈ S, 1 / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    have hsum3 : (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.log (T : ℝ) + 2 := by
      have hsub : S ⊆ Finset.Icc 1 T := by
        intro p hp
        have hpprime : p.Prime := hS p hp
        have hp2 : 2 ≤ p := hpprime.two_le
        rw [hSdef, Finset.mem_filter, Finset.mem_range] at hp
        rw [Finset.mem_Icc]
        exact ⟨by omega, by omega⟩
      have hle1 : (∑ p ∈ S, 1 / (p : ℝ))
          ≤ ∑ e ∈ Finset.Icc 1 T, 1 / (e : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro e _ _
        positivity
      have hle2 : (∑ e ∈ Finset.Icc 1 T, 1 / (e : ℝ)) = harmLogPow_aux 0 T := by
        unfold harmLogPow_aux
        apply Finset.sum_congr rfl
        intro e _
        simp
      have hb := harmLogPow_bound_aux 0 T
      rw [hle2] at hle1
      have hb2 : harmLogPow_aux 0 T ≤ Real.log (T : ℝ) + 2 := by
        have h := (abs_le.mp hb).2
        simp at h
        linarith
      exact le_trans hle1 hb2
    calc (∑ p ∈ S, ((localGoodChoiceFinset h i p hd he).card : ℝ)
            / ((p : ℝ) - 1))
        ≤ 2 * ((k : ℝ) + 1) ^ 2 * (∑ p ∈ S, 1 / (p : ℝ)) := by
          rw [← hsum2]
          exact hsum1
      _ ≤ 2 * ((k : ℝ) + 1) ^ 2 * (Real.log (T : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hsum3 (by positivity)
  calc ∑ n ∈ Finset.Icc 1 T, twistedAbsWeight h i hd he n
      ≤ ∏ p ∈ S, (1 + ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1)) := by rw [← hstep2]; exact hstep1
    _ ≤ Real.exp (∑ p ∈ S, ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1)) := hstep3
    _ ≤ Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (T : ℝ) + 2)) :=
        Real.exp_le_exp.mpr hstep4

/-- The same bound over a coprime class: filtering only removes
    nonnegative terms. -/
theorem solution {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {T : ℕ} (hT : 2 ≤ T) :
    ∑ n ∈ Finset.Icc 1 T, abs ((ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ))) ≤ Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (T : ℝ) + 2)) :=
  twistedAbsWeight_sum_Icc_le_exp_aux h i hd he hT
