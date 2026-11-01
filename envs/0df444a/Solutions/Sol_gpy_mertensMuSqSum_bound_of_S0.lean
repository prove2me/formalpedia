-- Prove2me | solution 1 for gpy_mertensMuSqSum_bound_of_S0
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T08:01:14.925587+00:00
-- url     : https://prove2.me/submissions/96b256c0-00f0-4814-bf9c-a5ed02e0a8e5

/- Submission file for `gpy` publish3 Mertens-partial problem gpy_mertensMuSqSum_bound_of_S0.
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

noncomputable def mertensWeight_aux (D : ℕ) : ℝ :=
  if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
    / ((Nat.totient D : ℕ) : ℝ) else 0

noncomputable def mertensMuSqSum_aux (m : ℕ) (T : ℕ) : ℝ :=
  ∑ D ∈ Finset.range (T + 1), mertensWeight_aux D * (Real.log (D : ℝ)) ^ m

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

theorem abel_sum_aux (a f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 1), a i * f i
      = (∑ i ∈ Finset.range (n + 1), a i) * f n
        - ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Finset.sum_range_succ (fun i => a i * f i) (n + 1)
    have h2 := Finset.sum_range_succ (fun i => a i) (n + 1)
    have h3 := Finset.sum_range_succ
      (fun i => (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i)) n
    rw [h1, h2, h3, ih]
    ring

theorem range_sum_one_div_eq_Icc_aux (N : ℕ) :
    (∑ e ∈ Finset.range (N + 1), (if e = 0 then (0 : ℝ) else 1 / (e : ℝ)))
      = ∑ e ∈ Finset.Icc 1 N, 1 / (e : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ N + 1 by omega),
      if_neg (Nat.succ_ne_zero N)]

theorem harmLogPow_abel_aux (m : ℕ) (T : ℕ) :
    harmLogPow_aux m T
      = (∑ e ∈ Finset.Icc 1 T, 1 / (e : ℝ)) * (Real.log (T : ℝ)) ^ m
        - ∑ i ∈ Finset.range T,
            (∑ e ∈ Finset.Icc 1 i, 1 / (e : ℝ))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by
  have h := abel_sum_aux (fun e => (if e = 0 then (0 : ℝ) else 1 / (e : ℝ)))
    (fun e => (Real.log (e : ℝ)) ^ m) T
  have hLHS : (∑ i ∈ Finset.range (T + 1),
        (if i = 0 then (0 : ℝ) else 1 / (i : ℝ)) * (Real.log (i : ℝ)) ^ m)
      = harmLogPow_aux m T := by
    have hterm : ∀ i : ℕ,
        (if i = 0 then (0 : ℝ) else 1 / (i : ℝ)) * (Real.log (i : ℝ)) ^ m
          = if i = 0 then (0 : ℝ) else (Real.log (i : ℝ)) ^ m / (i : ℝ) := by
      intro i
      by_cases hi : i = 0
      · subst hi
        simp
      · rw [if_neg hi, if_neg hi, mul_comm, ← div_eq_mul_one_div]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rw [Finset.sum_range_succ']
    have h0term : (if (0 : ℕ) = 0 then (0 : ℝ)
        else (Real.log ((0 : ℕ) : ℝ)) ^ m / ((0 : ℕ) : ℝ)) = 0 := if_pos rfl
    rw [h0term, add_zero]
    have h1 : (∑ i ∈ Finset.range T,
          (if i + 1 = 0 then (0 : ℝ)
            else (Real.log ((i + 1 : ℕ) : ℝ)) ^ m / ((i + 1 : ℕ) : ℝ)))
        = ∑ i ∈ Finset.range T,
          (Real.log ((i + 1 : ℕ) : ℝ)) ^ m / ((i + 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [if_neg (Nat.succ_ne_zero i)]
    rw [h1]
    exact (sum_Icc_one_eq_sum_range_aux
      (fun j => (Real.log (j : ℝ)) ^ m / (j : ℝ)) T).symm
  rw [hLHS] at h
  rw [h]
  congr 1
  · rw [range_sum_one_div_eq_Icc_aux]
  · apply Finset.sum_congr rfl
    intro i _
    rw [range_sum_one_div_eq_Icc_aux]

theorem harmLogPow_zero_aux (T : ℕ) :
    harmLogPow_aux 0 T = ∑ e ∈ Finset.Icc 1 T, 1 / (e : ℝ) := by
  unfold harmLogPow_aux
  apply Finset.sum_congr rfl
  intro e _
  simp

theorem log_pow_diff_nonneg_aux (m : ℕ) (i : ℕ) :
    (0 : ℝ) ≤ (Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m := by
  by_cases hi : i = 0
  · subst hi
    simp [Real.log_one, Real.log_zero]
  · have hnn : (0 : ℝ) ≤ Real.log (i : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ i))
    have hle : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith
    exact sub_nonneg.mpr (pow_le_pow_left₀ hnn hle m)

theorem sum_log_pow_diff_aux (m : ℕ) (T : ℕ) :
    ∑ i ∈ Finset.range T,
        ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m)
      = (Real.log (T : ℝ)) ^ m - (0 : ℝ) ^ m := by
  have h := Finset.sum_range_sub (fun i => (Real.log (i : ℝ)) ^ m) T
  rw [h]
  simp [Real.log_zero]

theorem mertensMuSqSum_abel_aux (m : ℕ) (T : ℕ) :
    mertensMuSqSum_aux m T
      = (∑ D ∈ Finset.range (T + 1), mertensWeight_aux D) * (Real.log (T : ℝ)) ^ m
        - ∑ i ∈ Finset.range T,
            (∑ D ∈ Finset.range (i + 1), mertensWeight_aux D)
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by
  unfold mertensMuSqSum_aux
  exact abel_sum_aux mertensWeight_aux (fun D => (Real.log (D : ℝ)) ^ m) T

theorem mertensMuSqSum_bound_of_S0_aux (m : ℕ) (T : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hS0 : ∀ i : ℕ,
      abs ((∑ D ∈ Finset.range (i + 1), mertensWeight_aux D) - Real.log (i : ℝ)) ≤ C₀) :
    abs (mertensMuSqSum_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ (6 + 2 * C₀) * (Real.log (T : ℝ)) ^ m := by
  by_cases hT0 : T = 0
  · subst hT0
    have hsum : mertensMuSqSum_aux m 0 = 0 := by
      unfold mertensMuSqSum_aux mertensWeight_aux
      simp
    rw [hsum]
    simp only [Nat.cast_zero, Real.log_zero, zero_pow (Nat.succ_ne_zero m),
      zero_div, sub_zero, abs_zero]
    by_cases hm : m = 0
    · subst hm
      simp only [pow_zero]
      linarith [hC₀]
    · rw [zero_pow (by omega : m ≠ 0)]
      simp
  have hT1 : 1 ≤ T := by omega
  have hlogT_nn : (0 : ℝ) ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hT1)
  have hP_nn : (0 : ℝ) ≤ (Real.log (T : ℝ)) ^ m := pow_nonneg hlogT_nn m
  -- Notation: partial sums, log-power differences, main bracket.
  set A : ℕ → ℝ := fun i => ∑ D ∈ Finset.range (i + 1), mertensWeight_aux D with hA
  set H : ℕ → ℝ := fun i => ∑ e ∈ Finset.Icc 1 i, 1 / (e : ℝ) with hH
  set Δ : ℕ → ℝ := fun i =>
    (Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m with hΔ
  have hΔ_nn : ∀ i, (0 : ℝ) ≤ Δ i := fun i => log_pow_diff_nonneg_aux m i
  have hΔ_sum : ∑ i ∈ Finset.range T, Δ i = (Real.log (T : ℝ)) ^ m - (0 : ℝ) ^ m :=
    sum_log_pow_diff_aux m T
  have hΔ_sum_le : ∑ i ∈ Finset.range T, Δ i ≤ (Real.log (T : ℝ)) ^ m := by
    rw [hΔ_sum]
    have : (0 : ℝ) ≤ (0 : ℝ) ^ m := pow_nonneg le_rfl m
    linarith
  have hΔ_tele : (Real.log (T : ℝ)) ^ (m + 1)
      = (Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m := by
    rw [pow_succ]
    ring
  -- Abel for mertensMuSqSum_aux.
  have habel := mertensMuSqSum_abel_aux m T
  -- The main bracket M.
  set M : ℝ := (Real.log (T : ℝ)) ^ (m + 1)
    - ∑ i ∈ Finset.range T, (Real.log (i : ℝ)) * Δ i with hM
  have hS_sub_M : abs (mertensMuSqSum_aux m T - M) ≤ 2 * C₀ * (Real.log (T : ℝ)) ^ m := by
    have hexpand : mertensMuSqSum_aux m T - M
        = (A T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m
          - ∑ i ∈ Finset.range T, (A i - Real.log (i : ℝ)) * Δ i := by
      rw [habel, hM, hΔ_tele]
      have hsum : (∑ i ∈ Finset.range T,
            (∑ D ∈ Finset.range (i + 1), mertensWeight_aux D)
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m))
          = (∑ i ∈ Finset.range T, (Real.log (i : ℝ))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m))
            + ∑ i ∈ Finset.range T,
              ((∑ D ∈ Finset.range (i + 1), mertensWeight_aux D) - Real.log (i : ℝ))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      simp only [hA, hΔ]
      ring
    rw [hexpand]
    have h1 : abs ((A T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m)
        ≤ C₀ * (Real.log (T : ℝ)) ^ m := by
      rw [abs_mul, abs_of_nonneg hP_nn]
      exact mul_le_mul_of_nonneg_right (hS0 T) hP_nn
    have h2 : abs (∑ i ∈ Finset.range T, (A i - Real.log (i : ℝ)) * Δ i)
        ≤ C₀ * (Real.log (T : ℝ)) ^ m := by
      calc abs (∑ i ∈ Finset.range T, (A i - Real.log (i : ℝ)) * Δ i)
          ≤ ∑ i ∈ Finset.range T, abs ((A i - Real.log (i : ℝ)) * Δ i) :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range T, C₀ * Δ i := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul, abs_of_nonneg (hΔ_nn i)]
            exact mul_le_mul_of_nonneg_right (hS0 i) (hΔ_nn i)
        _ = C₀ * (∑ i ∈ Finset.range T, Δ i) := by rw [Finset.mul_sum]
        _ ≤ C₀ * (Real.log (T : ℝ)) ^ m :=
            mul_le_mul_of_nonneg_left hΔ_sum_le hC₀
    calc abs ((A T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m
            - ∑ i ∈ Finset.range T, (A i - Real.log (i : ℝ)) * Δ i)
        ≤ abs ((A T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m)
          + abs (∑ i ∈ Finset.range T, (A i - Real.log (i : ℝ)) * Δ i) :=
          abs_sub _ _
      _ ≤ C₀ * (Real.log (T : ℝ)) ^ m + C₀ * (Real.log (T : ℝ)) ^ m := add_le_add h1 h2
      _ = 2 * C₀ * (Real.log (T : ℝ)) ^ m := by ring
  -- Abel for the harmonic sum, and its error vs M.
  have hH_bound : ∀ i : ℕ, abs (H i - Real.log (i : ℝ)) ≤ 2 := by
    intro i
    have h := harmLogPow_bound_aux 0 i
    rw [harmLogPow_zero_aux] at h
    have hcast : (Real.log (i : ℝ)) ^ (0 + 1) / (((0 : ℕ) : ℝ) + 1)
        = Real.log (i : ℝ) := by
      simp
    rw [hcast] at h
    simp only [pow_zero, mul_one] at h
    exact h
  have harm_abel := harmLogPow_abel_aux m T
  have hM_sub_harm : abs (M - harmLogPow_aux m T) ≤ 4 * (Real.log (T : ℝ)) ^ m := by
    have hexpand : M - harmLogPow_aux m T
        = -(H T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m
          + ∑ i ∈ Finset.range T, (H i - Real.log (i : ℝ)) * Δ i := by
      rw [harm_abel, hM, hΔ_tele]
      have hsum : (∑ i ∈ Finset.range T,
            (∑ e ∈ Finset.Icc 1 i, 1 / (e : ℝ))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m))
          = (∑ i ∈ Finset.range T, (Real.log (i : ℝ))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m))
            + ∑ i ∈ Finset.range T,
              ((∑ e ∈ Finset.Icc 1 i, 1 / (e : ℝ)) - Real.log (i : ℝ))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum]
      simp only [hH, hΔ]
      ring
    rw [hexpand]
    have h1 : abs (-(H T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m)
        ≤ 2 * (Real.log (T : ℝ)) ^ m := by
      rw [abs_mul, abs_neg, abs_of_nonneg hP_nn]
      exact mul_le_mul_of_nonneg_right (hH_bound T) hP_nn
    have h2 : abs (∑ i ∈ Finset.range T, (H i - Real.log (i : ℝ)) * Δ i)
        ≤ 2 * (Real.log (T : ℝ)) ^ m := by
      calc abs (∑ i ∈ Finset.range T, (H i - Real.log (i : ℝ)) * Δ i)
          ≤ ∑ i ∈ Finset.range T, abs ((H i - Real.log (i : ℝ)) * Δ i) :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range T, 2 * Δ i := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul, abs_of_nonneg (hΔ_nn i)]
            exact mul_le_mul_of_nonneg_right (hH_bound i) (hΔ_nn i)
        _ = 2 * (∑ i ∈ Finset.range T, Δ i) := by rw [Finset.mul_sum]
        _ ≤ 2 * (Real.log (T : ℝ)) ^ m :=
            mul_le_mul_of_nonneg_left hΔ_sum_le (by norm_num)
    calc abs (-(H T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m
            + ∑ i ∈ Finset.range T, (H i - Real.log (i : ℝ)) * Δ i)
        ≤ abs (-(H T - Real.log (T : ℝ)) * (Real.log (T : ℝ)) ^ m)
          + abs (∑ i ∈ Finset.range T, (H i - Real.log (i : ℝ)) * Δ i) :=
          abs_add_le _ _
      _ ≤ 2 * (Real.log (T : ℝ)) ^ m + 2 * (Real.log (T : ℝ)) ^ m := add_le_add h1 h2
      _ = 4 * (Real.log (T : ℝ)) ^ m := by ring
  have hharm : abs (harmLogPow_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ 2 * (Real.log (T : ℝ)) ^ m := harmLogPow_bound_aux m T
  calc abs (mertensMuSqSum_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ abs (mertensMuSqSum_aux m T - M) + abs (M - harmLogPow_aux m T)
        + abs (harmLogPow_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1)) := by
        have h1 := abs_sub_le (mertensMuSqSum_aux m T) M
          ((Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
        have h2 := abs_sub_le M (harmLogPow_aux m T)
          ((Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
        linarith [abs_sub_le (mertensMuSqSum_aux m T) M (harmLogPow_aux m T)]
    _ ≤ 2 * C₀ * (Real.log (T : ℝ)) ^ m + 4 * (Real.log (T : ℝ)) ^ m
        + 2 * (Real.log (T : ℝ)) ^ m := add_le_add (add_le_add hS_sub_M hM_sub_harm) hharm
    _ = (6 + 2 * C₀) * (Real.log (T : ℝ)) ^ m := by ring

theorem solution (m : ℕ) (T : ℕ) (C₀ : ℝ)
    (hC₀ : 0 ≤ C₀)
    (hS0 : ∀ i : ℕ,
      abs ((∑ D ∈ Finset.range (i + 1), (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
        / ((Nat.totient D : ℕ) : ℝ) else 0)) - Real.log (i : ℝ)) ≤ C₀) :
    abs ((∑ D ∈ Finset.range (T + 1),
      (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
        / ((Nat.totient D : ℕ) : ℝ) else 0) * (Real.log (D : ℝ)) ^ m)
      - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ (6 + 2 * C₀) * (Real.log (T : ℝ)) ^ m := by
  have hS0' : ∀ i : ℕ,
      abs ((∑ D ∈ Finset.range (i + 1), mertensWeight_aux D)
        - Real.log (i : ℝ)) ≤ C₀ := hS0
  exact mertensMuSqSum_bound_of_S0_aux m T C₀ hC₀ hS0'
