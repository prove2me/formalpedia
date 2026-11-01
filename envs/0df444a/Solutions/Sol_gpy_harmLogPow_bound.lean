-- Prove2me | solution 1 for gpy_harmLogPow_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T07:58:09.541149+00:00
-- url     : https://prove2.me/submissions/407e4fea-e5d5-4f75-9153-92594880c009

/- Submission file for `gpy` publish3 Mertens-partial problem gpy_harmLogPow_bound.
   Self-contained: imports Mathlib only. Top-level `theorem solution`
   in the problem's exact binder/statement form (statement mechanically
   extracted from the restated theorem, textually identical modulo the
   theorem name). All helpers are supporting bodies in this file; none
   is a separate problem. No sorry, no axioms beyond the standard ones,
   no platform imports. -/
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

theorem solution (m : ℕ) (T : ℕ) :
    abs ((∑ e ∈ Finset.Icc 1 T, (Real.log (e : ℝ)) ^ m / (e : ℝ))
      - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ 2 * (Real.log (T : ℝ)) ^ m :=
  harmLogPow_bound_aux m T
