-- Prove2me | solution 1 for gpy_mertensMuSqBound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T18:42:30.723774+00:00
-- url     : https://prove2.me/submissions/005d32c6-233f-4198-af97-e02a4ae9ad39

/- Submission file for `gpy` publishS0 problem: the unconditional Mertens bound for mu^2/phi-weighted log-power sums.
   Self-contained: imports Mathlib only. All local definitions and
   lemmas are supporting bodies with `_aux` names; the final theorem
   is stated in fully unfolded Mathlib-only terms and proved by
   conversion from the renamed original. No sorry, no platform imports,
   no PNT/Chebyshev input. -/
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



/-! ### The convolution factor c -/

/-- Local factor of `c` at prime `p` with exponent `e`:
    `1/(p-1)` at `e = 1`, `-p/(p-1)` at `e = 2`, `0` otherwise. -/
noncomputable def cLocal_aux (p : ℕ) (e : ℕ) : ℝ :=
  if e = 1 then 1 / ((p : ℝ) - 1)
  else if e = 2 then -((p : ℝ) / ((p : ℝ) - 1))
  else 0

/-- The convolution factor `c`, defined by its prime-power values:
    `c(p) = 1/(p-1)`, `c(p²) = -p/(p-1)`, `c(p^k) = 0` for `k ≥ 3`,
    extended multiplicatively over prime factors. `c 0 = 0`. -/
noncomputable def convC_aux (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ∏ p ∈ n.primeFactors, cLocal_aux p (n.factorization p)

theorem cLocal_zero_aux (p : ℕ) : cLocal_aux p 0 = 0 := by
  simp [cLocal_aux]

theorem convC_zero_aux : convC_aux 0 = 0 := by
  simp [convC_aux]

theorem convC_one_aux : convC_aux 1 = 1 := by
  simp [convC_aux]

theorem convC_prime_pow_aux {p : ℕ} (hp : p.Prime) (j : ℕ) :
    convC_aux (p ^ j) = if j = 0 then 1 else cLocal_aux p j := by
  by_cases hj : j = 0
  · subst hj
    simp [convC_one_aux]
  · have hpj : p ^ j ≠ 0 := pow_ne_zero j hp.ne_zero
    have hpf : (p ^ j).primeFactors = {p} := by
      rw [Nat.primeFactors_pow _ hj, hp.primeFactors]
    have hfac : (p ^ j).factorization p = j := by
      simp [hp.factorization_pow]
    simp only [convC_aux, if_neg hpj, hpf, Finset.prod_singleton, hfac, if_neg hj]

/-- `convC_aux` is multiplicative on coprime pairs. -/
theorem convC_mul_aux {m n : ℕ} (h : Nat.Coprime m n) :
    convC_aux (m * n) = convC_aux m * convC_aux n := by
  by_cases hm : m = 0
  · subst hm
    simp [convC_zero_aux]
  by_cases hn : n = 0
  · subst hn
    simp [convC_zero_aux]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have hdisj : Disjoint m.primeFactors n.primeFactors := h.disjoint_primeFactors
  have hfac : ∀ p ∈ m.primeFactors,
      (m * n).factorization p = m.factorization p := by
    intro p hp
    have hpn : p ∉ n.primeFactors := by
      intro hcon
      exact (Finset.disjoint_left.mp hdisj hp) hcon
    have hpdvd : ¬ p ∣ n := by
      intro hdvd
      exact hpn (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, hdvd, hn⟩)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpdvd, add_zero]
  have hfac' : ∀ p ∈ n.primeFactors,
      (m * n).factorization p = n.factorization p := by
    intro p hp
    have hpm : p ∉ m.primeFactors := by
      intro hcon
      exact (Finset.disjoint_right.mp hdisj hp) hcon
    have hpdvd : ¬ p ∣ m := by
      intro hdvd
      exact hpm (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, hdvd, hm⟩)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_add]
  simp only [convC_aux, if_neg hmn, if_neg hm, if_neg hn,
    Nat.primeFactors_mul hm hn, Finset.prod_union hdisj]
  congr 1
  · exact Finset.prod_congr rfl (fun p hp => by rw [hfac p hp])
  · exact Finset.prod_congr rfl (fun p hp => by rw [hfac' p hp])

/-! ### The divisor sum and the convolution identity b = 1 * c -/

/-- Divisor sum of `convC_aux`: the Dirichlet convolution `(1 * c)(n)`. -/
noncomputable def divSumC_aux (n : ℕ) : ℝ := ∑ d ∈ n.divisors, convC_aux d

theorem divSumC_one_aux : divSumC_aux 1 = 1 := by
  simp [divSumC_aux, convC_one_aux]

/-- Prime-power partial sums of `convC_aux`: `1` at `k = 0`, `p/(p-1)`
    at `k = 1`, `0` at `k ≥ 2` — the local sums that make the
    convolution collapse to `b`. -/
theorem sum_convC_prime_pow_aux {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), convC_aux (p ^ j)
      = if k = 0 then 1 else if k = 1 then (p : ℝ) / ((p : ℝ) - 1) else 0 := by
  induction k with
  | zero => simp [convC_one_aux]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
    by_cases hk0 : k = 0
    · subst hk0
      show (1 : ℝ) + convC_aux (p ^ 1) = (p : ℝ) / ((p : ℝ) - 1)
      rw [convC_prime_pow_aux hp 1]
      simp only [cLocal_aux, if_neg one_ne_zero, if_true]
      field_simp
      ring
    · by_cases hk1 : k = 1
      · subst hk1
        show (p : ℝ) / ((p : ℝ) - 1) + convC_aux (p ^ 2) = 0
        rw [convC_prime_pow_aux hp 2]
        simp only [cLocal_aux, if_neg (show (2 : ℕ) ≠ 0 by norm_num),
          if_neg (show (2 : ℕ) ≠ 1 by norm_num), if_true]
        ring
      · have hk2 : 2 ≤ k := by omega
        rw [if_neg hk0, if_neg hk1, if_neg (show k + 1 ≠ 0 by omega),
          if_neg (show k + 1 ≠ 1 by omega)]
        have hcp : convC_aux (p ^ (k + 1)) = 0 := by
          rw [convC_prime_pow_aux hp (k + 1)]
          simp only [if_neg (by omega : k + 1 ≠ 0), cLocal_aux,
            if_neg (by omega : k + 1 ≠ 1), if_neg (by omega : k + 1 ≠ 2)]
        rw [hcp, zero_add]

theorem divSumC_prime_pow_val_aux {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divSumC_aux (p ^ k)
      = if k = 0 then 1 else if k = 1 then (p : ℝ) / ((p : ℝ) - 1) else 0 := by
  rw [divSumC_aux, Nat.sum_divisors_prime_pow hp]
  exact sum_convC_prime_pow_aux hp k

/-- `convC_aux` as an arithmetic function. -/
noncomputable def convCAF_aux : ArithmeticFunction ℝ := ⟨convC_aux, convC_zero_aux⟩

theorem isMultiplicative_convCAF_aux : convCAF_aux.IsMultiplicative :=
  ⟨convC_one_aux, fun h => convC_mul_aux h⟩

/-- The divisor sum is the Dirichlet product `ζ * c`. -/
theorem divSumC_eq_zeta_mul_aux (n : ℕ) :
    divSumC_aux n = (ArithmeticFunction.zeta * convCAF_aux) n := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  rfl

/-- The divisor sum is multiplicative. -/
theorem divSumC_mul_aux {m n : ℕ} (h : Nat.Coprime m n) :
    divSumC_aux (m * n) = divSumC_aux m * divSumC_aux n := by
  rw [divSumC_eq_zeta_mul_aux, divSumC_eq_zeta_mul_aux, divSumC_eq_zeta_mul_aux]
  exact (ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    isMultiplicative_convCAF_aux).map_mul_of_coprime h

/-- The divisor sum factors over prime powers. -/
theorem divSumC_factorization_aux {n : ℕ} (hn : n ≠ 0) :
    divSumC_aux n = ∏ p ∈ n.primeFactors, divSumC_aux (p ^ n.factorization p) := by
  have h := Nat.multiplicative_factorization divSumC_aux
    (fun x y h => divSumC_mul_aux h) divSumC_one_aux hn
  rw [h]
  show (∏ p ∈ n.factorization.support, divSumC_aux (p ^ n.factorization p)) = _
  rw [Nat.support_factorization]

/-- `b n = n * mertensWeight_aux n`, so `b n / n` is the μ²/φ weight. -/
noncomputable def convB_aux (n : ℕ) : ℝ := (n : ℝ) * mertensWeight_aux n

/-- The convolution identity: `b = 1 * c`, i.e. `b n` equals the
    divisor sum of `convC_aux`. -/
theorem convB_eq_divSumC_aux (n : ℕ) : convB_aux n = divSumC_aux n := by
  by_cases hn : n = 0
  · subst hn
    simp [convB_aux, divSumC_aux]
  · rw [divSumC_factorization_aux hn]
    by_cases hsq : Squarefree n
    · have hfac : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
        intro p hp
        have hle := (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
        have hpos : 0 < n.factorization p := by
          have hne : n.factorization p ≠ 0 := by
            have hmem : p ∈ n.factorization.support := by
              rw [Nat.support_factorization]
              exact hp
            exact Finsupp.mem_support_iff.mp hmem
          omega
        omega
      have hprod : (∏ p ∈ n.primeFactors, divSumC_aux (p ^ n.factorization p))
          = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        rw [hfac p hp, divSumC_prime_pow_val_aux hpprime 1]
        simp
      have hphi : ((Nat.totient n : ℕ) : ℝ)
          = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
        have hmult : ∀ x y : ℕ, Nat.Coprime x y →
            (((Nat.totient (x * y) : ℕ)) : ℝ)
              = ((Nat.totient x : ℕ) : ℝ) * ((Nat.totient y : ℕ) : ℝ) := by
          intro x y hxy
          rw [Nat.totient_mul hxy]
          push_cast
          ring
        have h1 : (((Nat.totient 1 : ℕ)) : ℝ) = 1 := by simp
        have h := Nat.multiplicative_factorization
          (fun n => ((Nat.totient n : ℕ) : ℝ)) hmult h1 hn
        rw [h]
        show (∏ p ∈ n.factorization.support,
            ((Nat.totient (p ^ n.factorization p) : ℕ) : ℝ)) = _
        rw [Nat.support_factorization]
        apply Finset.prod_congr rfl
        intro p hp
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        rw [hfac p hp, pow_one, Nat.totient_prime hpprime]
        rw [Nat.cast_sub (by exact_mod_cast hpprime.one_le : (1 : ℕ) ≤ p)]
        push_cast
        ring
      have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
        have h0 := Nat.prod_factorization_pow_eq_self hn
        have h1 : n.factorization.prod (· ^ ·)
            = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
          show (∏ p ∈ n.factorization.support, p ^ n.factorization p) = _
          rw [Nat.support_factorization]
        rw [h1] at h0
        have hcast : (n : ℝ)
            = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℝ) := by
          rw [h0]
        rw [hcast]
        push_cast
        apply Finset.prod_congr rfl
        intro p hp
        rw [hfac p hp, pow_one]
      have hmu : ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      rw [hprod, convB_aux, mertensWeight_aux, if_pos hsq, hmu, hnprod, hphi,
        ← div_eq_mul_one_div, Finset.prod_div_distrib]
    · have hex : ∃ p, 2 ≤ n.factorization p := by
        by_contra hc
        push Not at hc
        exact hsq (Nat.squarefree_of_factorization_le_one hn
          (fun p => by have := hc p; omega))
      obtain ⟨p, hp2⟩ := hex
      have hpmem : p ∈ n.primeFactors := by
        have hne : n.factorization p ≠ 0 := by omega
        have hprime : p.Prime := by
          by_contra hnp
          exact hne (Nat.factorization_eq_zero_of_not_prime n hnp)
        have hdvd : p ∣ n := by
          have h1 : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
          exact dvd_trans (dvd_pow_self p (by omega : n.factorization p ≠ 0)) h1
        exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn⟩
      have hzero : divSumC_aux (p ^ n.factorization p) = 0 := by
        rw [divSumC_prime_pow_val_aux (Nat.mem_primeFactors.mp hpmem).1]
        simp [show n.factorization p ≠ 0 by omega,
          show n.factorization p ≠ 1 by omega]
      rw [Finset.prod_eq_zero hpmem hzero]
      simp [convB_aux, mertensWeight_aux, if_neg hsq]

/-! ### Truncated Euler products -/

/-- `truncSet_aux S`: numbers `d ≥ 1` whose prime factors lie in `S`
    and whose prime exponents are at most `2`. -/
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

/-- The absolute weight `w d = |convC_aux d| / d`. -/
noncomputable def wAbs_aux (d : ℕ) : ℝ := |convC_aux d| / (d : ℝ)

theorem wAbs_one_aux : wAbs_aux 1 = 1 := by
  simp [wAbs_aux, convC_one_aux]

theorem wAbs_mul_aux {m n : ℕ} (h : Nat.Coprime m n) :
    wAbs_aux (m * n) = wAbs_aux m * wAbs_aux n := by
  have h1 : wAbs_aux (m * n) = |convC_aux m| * |convC_aux n| / ((m : ℝ) * (n : ℝ)) := by
    show |convC_aux (m * n)| / ((m * n : ℕ) : ℝ) = _
    rw [convC_mul_aux h, abs_mul, Nat.cast_mul]
  have h2 : wAbs_aux m * wAbs_aux n = |convC_aux m| * |convC_aux n| / ((m : ℝ) * (n : ℝ)) := by
    show (|convC_aux m| / (m : ℝ)) * (|convC_aux n| / (n : ℝ)) = _
    rw [div_mul_div_comm]
  rw [h1, h2]

/-- Local value of `wAbs_aux` at `p^1`. -/
theorem wAbs_prime_pow_one_aux {p : ℕ} (hp : p.Prime) :
    wAbs_aux (p ^ 1) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpos1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  show |convC_aux (p ^ 1)| / ((p ^ 1 : ℕ) : ℝ) = _
  rw [convC_prime_pow_aux hp 1]
  simp only [if_neg one_ne_zero, cLocal_aux, if_true]
  rw [pow_one, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((p : ℝ) - 1)),
    div_div, mul_comm ((p : ℝ) - 1) (p : ℝ)]

/-- Local value of `wAbs_aux` at `p^2`. -/
theorem wAbs_prime_pow_two_aux {p : ℕ} (hp : p.Prime) :
    wAbs_aux (p ^ 2) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpos1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  show |convC_aux (p ^ 2)| / ((p ^ 2 : ℕ) : ℝ) = _
  rw [convC_prime_pow_aux hp 2]
  simp only [if_neg (show (2 : ℕ) ≠ 0 by norm_num), cLocal_aux,
    if_neg (show (2 : ℕ) ≠ 1 by norm_num), if_true]
  rw [Nat.cast_pow]
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) / ((p : ℝ) - 1))]
  field_simp

/-- Local sums of `wAbs_aux` at prime powers: `1 + 2 / (p (p-1))`. -/
theorem sum_wAbs_prime_pow_aux {p : ℕ} (hp : p.Prime) :
    ∑ j ∈ Finset.range 3, wAbs_aux (p ^ j)
      = 1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  have hw0 : wAbs_aux (p ^ 0) = 1 := by simp [wAbs_aux, convC_one_aux]
  rw [hw0, wAbs_prime_pow_one_aux hp, wAbs_prime_pow_two_aux hp]
  ring

theorem sum_truncSet_wAbs_eq_prod_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ truncSet_aux S, wAbs_aux d
      = ∏ p ∈ S, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  rw [sum_truncSet_eq_prod_aux wAbs_aux wAbs_one_aux (fun _ _ h => wAbs_mul_aux h) S hS]
  apply Finset.prod_congr rfl
  intro p hp
  exact sum_wAbs_prime_pow_aux (hS p hp)

/-- The truncated `wAbs_aux` sum over any prime finset is at most `e²`. -/
theorem sum_truncSet_wAbs_le_exp_two_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ truncSet_aux S, wAbs_aux d ≤ Real.exp 2 := by
  rw [sum_truncSet_wAbs_eq_prod_aux hS]
  have h1 : ∏ p ∈ S, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1)))
      ≤ ∏ p ∈ S, Real.exp (2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
      have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by
        apply mul_pos (by linarith) (by linarith)
      positivity
    · intro p hp
      have h := Real.add_one_le_exp (2 / ((p : ℝ) * ((p : ℝ) - 1)))
      linarith
  rw [← Real.exp_sum] at h1
  have h2 : (∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 2 := by
    by_cases hSe : S = ∅
    · subst hSe
      simp
    · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
      have hp02 : 2 ≤ p₀ := (hS p₀ hp₀).two_le
      have hM : 2 ≤ S.sup id := by
        have hle : p₀ ≤ S.sup id := Finset.le_sup (f := id) hp₀
        omega
      have hsub : S ⊆ Finset.Icc 2 (S.sup id) := by
        intro p hp
        simp only [Finset.mem_Icc]
        refine ⟨(hS p hp).two_le, ?_⟩
        exact Finset.le_sup (f := id) hp
      have hle1 : (∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 1)))
          ≤ ∑ n ∈ Finset.Icc 2 (S.sup id), 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n hn _
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
          apply mul_pos (by linarith) (by linarith)
        positivity
      have hsum : (∑ n ∈ Finset.Icc 2 (S.sup id), 2 / ((n : ℝ) * ((n : ℝ) - 1)))
          = 2 * (1 - 1 / ((S.sup id : ℕ) : ℝ)) := by
        have hterm : ∀ n ∈ Finset.Icc 2 (S.sup id),
            2 / ((n : ℝ) * ((n : ℝ) - 1))
              = 2 * (1 / (((n : ℝ) - 1) * (n : ℝ))) := by
          intro n _
          rw [mul_comm ((n : ℝ)) ((n : ℝ) - 1), mul_one_div]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
          sum_inv_mul_pred_aux (by omega : 1 ≤ S.sup id)]
      calc (∑ p ∈ S, 2 / ((p : ℝ) * ((p : ℝ) - 1)))
          ≤ 2 * (1 - 1 / ((S.sup id : ℕ) : ℝ)) := by rw [← hsum]; exact hle1
        _ ≤ 2 := by
          have hMpos : (0 : ℝ) < ((S.sup id : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 0 < S.sup id)
          have hnn : (0 : ℝ) ≤ 1 / ((S.sup id : ℕ) : ℝ) := by positivity
          linarith
  exact le_trans h1 (Real.exp_le_exp.mpr h2)

/-- The range sum of `wAbs_aux` is at most `e²` (the C₂ bound). -/
theorem sum_range_wAbs_le_exp_two_aux (T : ℕ) :
    ∑ d ∈ Finset.range (T + 1), wAbs_aux d ≤ Real.exp 2 := by
  set S := (Finset.range (T + 1)).filter (fun p => p.Prime) with hSdef
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hle : (∑ d ∈ Finset.range (T + 1), wAbs_aux d) ≤ ∑ d ∈ truncSet_aux S, wAbs_aux d := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (T + 1))
      (fun d => d ∈ truncSet_aux S) wAbs_aux
    have hzero : ∑ d ∈ (Finset.range (T + 1)).filter (fun d => d ∉ truncSet_aux S),
        wAbs_aux d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hdT : d ∈ Finset.range (T + 1) := (Finset.mem_filter.mp hd).1
      have hdnot : d ∉ truncSet_aux S := (Finset.mem_filter.mp hd).2
      by_cases hconv : convC_aux d = 0
      · show |convC_aux d| / (d : ℝ) = 0
        rw [hconv]
        simp
      · exfalso
        apply hdnot
        rw [mem_truncSet_aux hS2]
        have hd0 : d ≠ 0 := by
          intro h0
          subst h0
          exact hconv convC_zero_aux
        refine ⟨by omega, ?_⟩
        intro p hp
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
        have hple : p ≤ d := Nat.le_of_dvd (by omega) hpdvd
        have hpT : p ∈ Finset.range (T + 1) := by
          rw [Finset.mem_range]
          have hdT' : d < T + 1 := Finset.mem_range.mp hdT
          omega
        refine ⟨?_, ?_⟩
        · rw [hSdef, Finset.mem_filter]
          exact ⟨hpT, hpprime⟩
        · by_contra hcon
          push Not at hcon
          have hzero2 : convC_aux d = 0 := by
            show (if d = 0 then (0 : ℝ)
              else ∏ q ∈ d.primeFactors, cLocal_aux q (d.factorization q)) = 0
            rw [if_neg hd0]
            apply Finset.prod_eq_zero hp
            show cLocal_aux p (d.factorization p) = 0
            simp only [cLocal_aux, if_neg (by omega : d.factorization p ≠ 1),
              if_neg (by omega : d.factorization p ≠ 2)]
          exact hconv hzero2
    rw [← hsplit, hzero, add_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d _ _
      show (0 : ℝ) ≤ |convC_aux d| / (d : ℝ)
      positivity
  exact le_trans hle (sum_truncSet_wAbs_le_exp_two_aux hS)

/-! ### The log-weighted bound `∑ w d log d ≤ 24 e²` -/

/-- Log of a truncated number as a sum over its prime factors. -/
theorem log_truncSet_eq_sum_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {d : ℕ} (hd : d ∈ truncSet_aux S) :
    Real.log (d : ℝ) = ∑ p ∈ S, (d.factorization p : ℝ) * Real.log (p : ℝ) := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  obtain ⟨hd1, hdcond⟩ := (mem_truncSet_aux hS2).mp hd
  have hd0 : d ≠ 0 := by omega
  have hdprod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ d.factorization p := by
    have h0 := Nat.prod_factorization_pow_eq_self hd0
    have h1 : d.factorization.prod (· ^ ·)
        = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
      show (∏ p ∈ d.factorization.support, p ^ d.factorization p) = _
      rw [Nat.support_factorization]
    rw [h1] at h0
    have hcast : ((∏ p ∈ d.primeFactors, p ^ d.factorization p : ℕ) : ℝ) = (d : ℝ) := by
      rw [h0]
    rw [← hcast, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p hp => Nat.cast_pow p (d.factorization p))
  rw [hdprod]
  rw [Real.log_prod (fun p hp => pow_ne_zero _
    (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero))]
  have hlogpow : (∑ i ∈ d.primeFactors, Real.log ((i : ℝ) ^ d.factorization i))
      = ∑ i ∈ d.primeFactors, (d.factorization i : ℝ) * Real.log (i : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact Real.log_pow (p : ℝ) (d.factorization p)
  rw [hlogpow]
  apply Finset.sum_subset
  · intro p hp
    exact (hdcond p hp).1
  · intro p hpS hpnot
    have hprime : p.Prime := hS p hpS
    have hnotdvd : ¬ p ∣ d := by
      intro hdvd
      exact hpnot (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hd0⟩)
    have h0 : d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnotdvd
    rw [h0]
    simp

/-- One-coordinate sum: the `p`-coordinate of `∑ v_p(d) wAbs_aux d` over a truncated set. -/
theorem sum_truncSet_factorization_mul_wAbs_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {p : ℕ} (hp : p ∈ S) :
    ∑ d ∈ truncSet_aux S, (d.factorization p : ℝ) * wAbs_aux d
      = (3 / ((p : ℝ) * ((p : ℝ) - 1)))
        * ∑ d₀ ∈ truncSet_aux (S.erase p), wAbs_aux d₀ := by
  have hpprime : p.Prime := hS p hp
  have hSeq : insert p (S.erase p) = S := Finset.insert_erase hp
  have hS' : ∀ q ∈ S.erase p, q.Prime := fun q hq => hS q (Finset.mem_of_mem_erase hq)
  have hnot : p ∉ S.erase p := Finset.notMem_erase p S
  have hS2 : ∀ q ∈ S.erase p, 2 ≤ q := fun q hq => (hS' q hq).two_le
  have h1 : ∑ d ∈ truncSet_aux S, (d.factorization p : ℝ) * wAbs_aux d
      = ∑ d₀ ∈ truncSet_aux (S.erase p), ∑ j ∈ Finset.range 3,
          ((d₀ * p ^ j).factorization p : ℝ) * wAbs_aux (d₀ * p ^ j) := by
    have h2 := sum_truncSet_insert_aux hS' hpprime hnot
      (fun d => (d.factorization p : ℝ) * wAbs_aux d)
    rw [hSeq] at h2
    exact h2
  rw [h1]
  trans (∑ d₀ ∈ truncSet_aux (S.erase p),
    wAbs_aux d₀ * (∑ j ∈ Finset.range 3, (j : ℝ) * wAbs_aux (p ^ j)))
  · apply Finset.sum_congr rfl
    intro d₀ hd₀
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hd00 : d₀ ≠ 0 := by
      have h1' := ((mem_truncSet_aux hS2).mp hd₀).1
      omega
    have hnotdvd : ¬ p ∣ d₀ := by
      intro hdvd
      exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hd₀ hnot
        (Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, hd00⟩)
    have hfac : (d₀ * p ^ j).factorization p = j :=
      factorization_mul_pow_aux hpprime hd00
        (not_mem_primeFactors_of_mem_truncSet_aux hS2 hd₀ hnot)
    have hcop : Nat.Coprime d₀ (p ^ j) :=
      ((hpprime.coprime_iff_not_dvd.mpr hnotdvd).symm).pow_right j
    rw [hfac, wAbs_mul_aux hcop]
    ring
  · have hinner : (∑ j ∈ Finset.range 3, (j : ℝ) * wAbs_aux (p ^ j))
        = 3 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Finset.sum_range_zero, zero_add]
      rw [wAbs_prime_pow_one_aux hpprime, wAbs_prime_pow_two_aux hpprime]
      ring
    rw [hinner, ← Finset.sum_mul]
    exact mul_comm _ _

/-- The square-root telescoping identity, by induction on `M`. -/
theorem sum_sqrt_diff_aux (M : ℕ) (hM : 2 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ))
      = 1 - 1 / Real.sqrt (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    norm_num [Real.sqrt_one]
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1), ih]
    have hcast : (((k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by push_cast; ring
    rw [hcast]
    ring

/-- Per-term square-root bound: `4 / (n √n) ≤ 8 (1/√(n-1) - 1/√n)`. -/
theorem four_div_sqrt_le_aux (n : ℕ) (hn : 2 ≤ n) :
    (4 : ℝ) / ((n : ℝ) * Real.sqrt (n : ℝ))
      ≤ 8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  set a := Real.sqrt ((n : ℝ) - 1) with ha
  set b := Real.sqrt (n : ℝ) with hb
  have ha0 : (0 : ℝ) < a := by rw [ha]; exact Real.sqrt_pos.mpr (by linarith)
  have hb0 : (0 : ℝ) < b := by rw [hb]; exact Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = (n : ℝ) - 1 := by rw [ha]; exact Real.sq_sqrt hn1
  have hb2 : b ^ 2 = (n : ℝ) := by rw [hb]; exact Real.sq_sqrt hn0
  have hab_le : a ≤ b := by
    rw [ha, hb]; exact Real.sqrt_le_sqrt (by linarith)
  have hba : b - a = 1 / (b + a) := by
    rw [eq_div_iff (show (b + a) ≠ 0 from ne_of_gt (by linarith))]
    have h : (b - a) * (b + a) = b ^ 2 - a ^ 2 := by ring
    rw [h, hb2, ha2]
    ring
  have hdiff : 1 / a - 1 / b = 1 / (a * b * (b + a)) := by
    rw [div_sub_div _ _ (ne_of_gt ha0) (ne_of_gt hb0)]
    rw [one_mul, mul_one, hba, div_div]
    congr 1
    ring
  have hprod_le : a * b * (b + a) ≤ 2 * (n : ℝ) * b := by
    have h1 : a * b * (b + a) ≤ b * b * (2 * b) := by
      apply mul_le_mul
      · exact mul_le_mul hab_le (le_refl b) (le_of_lt hb0) (le_of_lt hb0)
      · linarith [hab_le]
      · linarith [ha0, hb0]
      · exact mul_nonneg (le_of_lt hb0) (le_of_lt hb0)
    have hbb : b * b = (n : ℝ) := by rw [← pow_two]; exact hb2
    calc a * b * (b + a) ≤ b * b * (2 * b) := h1
      _ = 2 * (n : ℝ) * b := by rw [hbb]; ring
  have hdiff_ge : 1 / (2 * (n : ℝ) * b) ≤ 1 / a - 1 / b := by
    rw [hdiff]
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos ha0 hb0) (by linarith)
    · exact hprod_le
  calc (4 : ℝ) / ((n : ℝ) * b) = 8 * (1 / (2 * (n : ℝ) * b)) := by
        rw [mul_one_div,
          div_eq_div_iff (ne_of_gt (mul_pos (by linarith) hb0))
            (ne_of_gt (mul_pos (mul_pos (by norm_num) (by linarith)) hb0))]
        ring
    _ ≤ 8 * (1 / a - 1 / b) := by
        apply mul_le_mul_of_nonneg_left hdiff_ge (by norm_num)

/-- The log-over-`n(n-1)` term is at most `4 / (n √n)`, via `log n ≤ 2 √n`. -/
theorem log_div_le_four_div_sqrt_aux {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ 4 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hden1 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    apply mul_pos (by linarith) (by linarith)
  have hden2 : (0 : ℝ) < (n : ℝ) * Real.sqrt (n : ℝ) := by
    apply mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith))
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
    have h1 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
      have h := Real.log_pow (Real.sqrt (n : ℝ)) 2
      rw [hsq] at h
      rw [h]
      ring
    have h2 : Real.log (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
    linarith [h1, h2]
  have hne1 : ((n : ℝ) * ((n : ℝ) - 1)) ≠ 0 := ne_of_gt hden1
  have hne2 : ((n : ℝ) * Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt hden2
  field_simp
  have hsq2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt hn0
  have h2n : Real.log (n : ℝ) * Real.sqrt (n : ℝ) ≤ 2 * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg (n : ℝ))
    have h3 : (2 : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = 2 * (n : ℝ) := by
      rw [mul_assoc, hsq2]
    rwa [h3] at h
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [div_le_iff₀ hpos]
  linarith [h2n, hn2]

/-- The prime sum `∑_{p ∈ S} log p / (p (p-1)) ≤ 8`. -/
theorem sum_log_div_le_eight_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 8 := by
  by_cases hSe : S = ∅
  · subst hSe
    simp
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
    have hM : 2 ≤ S.sup id := by
      have hle : p₀ ≤ S.sup id := Finset.le_sup (f := id) hp₀
      have hp02 : 2 ≤ p₀ := (hS p₀ hp₀).two_le
      omega
    have hsub : S ⊆ Finset.Icc 2 (S.sup id) := by
      intro p hp
      simp only [Finset.mem_Icc]
      refine ⟨(hS p hp).two_le, ?_⟩
      exact Finset.le_sup (f := id) hp
    calc ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ n ∈ Finset.Icc 2 (S.sup id),
            Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro n hn _
          have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
            apply mul_pos (by linarith) (by linarith)
          have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
          positivity
      _ ≤ ∑ n ∈ Finset.Icc 2 (S.sup id), 4 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact log_div_le_four_div_sqrt_aux (Finset.mem_Icc.mp hn).1
      _ ≤ ∑ n ∈ Finset.Icc 2 (S.sup id),
            8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact four_div_sqrt_le_aux n (Finset.mem_Icc.mp hn).1
      _ = 8 * (1 - 1 / Real.sqrt ((S.sup id : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum, sum_sqrt_diff_aux _ hM]
      _ ≤ 8 := by
          have hnn : (0 : ℝ) ≤ 1 / Real.sqrt ((S.sup id : ℕ) : ℝ) := by positivity
          linarith

/-- The log-weighted truncated bound: `∑ w d log d ≤ 24 e²`. -/
theorem sum_truncSet_wAbs_log_le_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ truncSet_aux S, wAbs_aux d * Real.log (d : ℝ) ≤ 24 * Real.exp 2 := by
  calc ∑ d ∈ truncSet_aux S, wAbs_aux d * Real.log (d : ℝ)
      = ∑ d ∈ truncSet_aux S, ∑ p ∈ S,
          wAbs_aux d * ((d.factorization p : ℝ) * Real.log (p : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [log_truncSet_eq_sum_aux hS hd, Finset.mul_sum]
    _ = ∑ p ∈ S, ∑ d ∈ truncSet_aux S,
          wAbs_aux d * ((d.factorization p : ℝ) * Real.log (p : ℝ)) := by
        rw [Finset.sum_comm]
    _ = ∑ p ∈ S, Real.log (p : ℝ) * ((3 / ((p : ℝ) * ((p : ℝ) - 1)))
          * ∑ d₀ ∈ truncSet_aux (S.erase p), wAbs_aux d₀) := by
        apply Finset.sum_congr rfl
        intro p hp
        have h1 : ∑ d ∈ truncSet_aux S, wAbs_aux d * ((d.factorization p : ℝ) * Real.log (p : ℝ))
            = Real.log (p : ℝ) * ∑ d ∈ truncSet_aux S, (d.factorization p : ℝ) * wAbs_aux d := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
        rw [h1, sum_truncSet_factorization_mul_wAbs_aux hS hp]
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) * ((3 / ((p : ℝ) * ((p : ℝ) - 1)))
          * Real.exp 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpprime : p.Prime := hS p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
        have hlog : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
        have h3 : (0 : ℝ) ≤ 3 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by
            apply mul_pos (by linarith) (by linarith)
          positivity
        have herase : ∑ d₀ ∈ truncSet_aux (S.erase p), wAbs_aux d₀ ≤ Real.exp 2 :=
          sum_truncSet_wAbs_le_exp_two_aux (fun q hq => hS q (Finset.mem_of_mem_erase hq))
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herase h3) hlog
    _ = 3 * Real.exp 2 * ∑ p ∈ S,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        trans ∑ p ∈ S, (3 * Real.exp 2)
          * (Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
        · apply Finset.sum_congr rfl
          intro p hp
          ring
        · rw [← Finset.mul_sum]
    _ ≤ 3 * Real.exp 2 * 8 := by
        apply mul_le_mul_of_nonneg_left (sum_log_div_le_eight_aux hS) (by positivity)
    _ = 24 * Real.exp 2 := by ring

/-- A number with `convC_aux d ≠ 0` and `d ≤ T` lies in the truncated set over primes `≤ T`. -/
theorem mem_truncSet_of_convC_ne_zero_aux {T : ℕ} {d : ℕ}
    (hdT : d ∈ Finset.range (T + 1)) (hconv : convC_aux d ≠ 0) :
    d ∈ truncSet_aux ((Finset.range (T + 1)).filter (fun p => p.Prime)) := by
  set S := (Finset.range (T + 1)).filter (fun p => p.Prime) with hSdef
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  rw [mem_truncSet_aux hS2]
  have hd0 : d ≠ 0 := by
    intro h0
    subst h0
    exact hconv convC_zero_aux
  refine ⟨by omega, ?_⟩
  intro p hp
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
  have hple : p ≤ d := Nat.le_of_dvd (by omega) hpdvd
  have hpT : p ∈ Finset.range (T + 1) := by
    rw [Finset.mem_range]
    have hdT' : d < T + 1 := Finset.mem_range.mp hdT
    omega
  refine ⟨?_, ?_⟩
  · rw [hSdef, Finset.mem_filter]
    exact ⟨hpT, hpprime⟩
  · by_contra hcon
    push Not at hcon
    have hzero2 : convC_aux d = 0 := by
      show (if d = 0 then (0 : ℝ)
        else ∏ q ∈ d.primeFactors, cLocal_aux q (d.factorization q)) = 0
      rw [if_neg hd0]
      apply Finset.prod_eq_zero hp
      show cLocal_aux p (d.factorization p) = 0
      simp only [cLocal_aux, if_neg (by omega : d.factorization p ≠ 1),
        if_neg (by omega : d.factorization p ≠ 2)]
    exact hconv hzero2

/-! ### The signed weight and its truncated sum -/

/-- The signed weight `c(d) / d`. -/
noncomputable def wSigned_aux (d : ℕ) : ℝ := convC_aux d / (d : ℝ)

theorem wSigned_one_aux : wSigned_aux 1 = 1 := by
  simp [wSigned_aux, convC_one_aux]

theorem wSigned_mul_aux {m n : ℕ} (h : Nat.Coprime m n) :
    wSigned_aux (m * n) = wSigned_aux m * wSigned_aux n := by
  show convC_aux (m * n) / ((m * n : ℕ) : ℝ) = (convC_aux m / (m : ℝ)) * (convC_aux n / (n : ℝ))
  rw [convC_mul_aux h, Nat.cast_mul, div_mul_div_comm]

/-- The signed truncated sum is exactly `1`. -/
theorem sum_truncSet_wSigned_eq_one_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ truncSet_aux S, wSigned_aux d = 1 := by
  rw [sum_truncSet_eq_prod_aux wSigned_aux wSigned_one_aux (fun _ _ h => wSigned_mul_aux h) S hS]
  apply Finset.prod_eq_one
  intro p hp
  have hpprime : p.Prime := hS p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  have e0 : wSigned_aux (p ^ 0) = 1 := by simp [wSigned_aux, convC_one_aux]
  have e1 : wSigned_aux (p ^ 1) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    show convC_aux (p ^ 1) / ((p ^ 1 : ℕ) : ℝ) = _
    rw [convC_prime_pow_aux hpprime 1]
    simp only [if_neg one_ne_zero, cLocal_aux, if_true]
    rw [pow_one, div_div, mul_comm ((p : ℝ) - 1) (p : ℝ)]
  have e2 : wSigned_aux (p ^ 2) = -1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    show convC_aux (p ^ 2) / ((p ^ 2 : ℕ) : ℝ) = _
    rw [convC_prime_pow_aux hpprime 2]
    simp only [if_neg (show (2 : ℕ) ≠ 0 by norm_num), cLocal_aux,
      if_neg (show (2 : ℕ) ≠ 1 by norm_num), if_true]
    rw [Nat.cast_pow]
    field_simp
  rw [e0, e1, e2]
  ring

/-! ### Stage 4: the swap, harmonic errors, and assembly -/

/-- Nonnegativity of `wAbs_aux`. -/
theorem wAbs_nonneg_aux (d : ℕ) : (0 : ℝ) ≤ wAbs_aux d := by
  show (0 : ℝ) ≤ abs (convC_aux d) / (d : ℝ)
  positivity

/-- Absolute value of a signed term is the absolute weight. -/
theorem abs_convC_div_aux (d : ℕ) : abs (convC_aux d / (d : ℝ)) = wAbs_aux d := by
  show abs (convC_aux d / (d : ℝ)) = abs (convC_aux d) / (d : ℝ)
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ))]

/-- Absolute value of the signed weight. -/
theorem abs_wSigned_aux (d : ℕ) : abs (wSigned_aux d) = wAbs_aux d := by
  show abs (convC_aux d / (d : ℝ)) = wAbs_aux d
  exact abs_convC_div_aux d

/-- `mertensWeight_aux` vanishes at `0`. -/
theorem mertensWeight_zero_aux : mertensWeight_aux 0 = 0 := by
  have hnot : ¬ Squarefree (0 : ℕ) := by
    intro h
    have h2 := h 2 (dvd_zero _)
    rw [Nat.isUnit_iff] at h2
    norm_num at h2
  simp only [mertensWeight_aux, if_neg hnot]

/-- `mertensWeight_aux` is `1` at `1`. -/
theorem mertensWeight_one_aux : mertensWeight_aux 1 = 1 := by
  have hsq : Squarefree (1 : ℕ) := squarefree_one
  simp only [mertensWeight_aux, if_pos hsq]
  rw [ArithmeticFunction.moebius_apply_one, Nat.totient_one]
  simp

/-- Division comparison for naturals, both directions, from first principles. -/
theorem nat_le_div_iff_mul_le_aux {m T d : ℕ} (hd : 0 < d) :
    m ≤ T / d ↔ m * d ≤ T := by
  constructor
  · intro h
    exact le_trans (mul_le_mul h (le_refl d) (Nat.zero_le d) (Nat.zero_le _)) (Nat.div_mul_le_self T d)
  · intro h
    by_contra hcon
    push Not at hcon
    have h1 := Nat.div_add_mod T d
    have h2 := Nat.mod_lt T hd
    have h3 : (T / d + 1) * d ≤ m * d := mul_le_mul (by omega) (le_refl d) (Nat.zero_le d) (Nat.zero_le _)
    have h4 : (T / d + 1) * d = d * (T / d) + d := by ring
    omega

/-- The harmonic error at `m = 0` is at most `2`. -/
theorem harm_err_le_two_aux (M : ℕ) :
    abs (harmLogPow_aux 0 M - Real.log (M : ℝ)) ≤ 2 := by
  have h := harmLogPow_bound_aux 0 M
  simpa using h

/-- The error from replacing `log (T/d)` (nat division) by `log T - log d` is at most `1`. -/
theorem log_div_nat_err_aux (T d : ℕ) (hd : 1 ≤ d) (hdT : d ≤ T) :
    abs (Real.log ((T / d : ℕ) : ℝ) - Real.log ((T : ℝ) / (d : ℝ))) ≤ 1 := by
  have hd0 : 0 < d := by omega
  have hT0 : 0 < T := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT0
  set M := T / d with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.div_pos hdT hd0
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hMle : (M : ℝ) ≤ (T : ℝ) / (d : ℝ) := by
    rw [hMdef]
    exact Nat.cast_div_le
  have hlt : (T : ℝ) / (d : ℝ) < (M : ℝ) + 1 := by
    have h1 := Nat.div_add_mod T d
    rw [← hMdef] at h1
    have h2 := Nat.mod_lt T hd0
    have hnat : T < (M + 1) * d := by
      have h4 : (M + 1) * d = d * M + d := by ring
      omega
    have hcast : (T : ℝ) < (((M + 1) * d : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
    rw [div_lt_iff₀ hdpos]
    exact hcast
  have hlogle : Real.log (M : ℝ) ≤ Real.log ((T : ℝ) / (d : ℝ)) :=
    Real.log_le_log hMpos hMle
  have h1 : Real.log ((T : ℝ) / (d : ℝ)) - Real.log (M : ℝ) ≤ 1 := by
    rw [← Real.log_div (ne_of_gt (div_pos hTpos hdpos)) (ne_of_gt hMpos)]
    have hle2 : ((T : ℝ) / (d : ℝ)) / (M : ℝ) ≤ 1 + 1 / (M : ℝ) := by
      rw [div_le_iff₀ hMpos]
      have heq : (1 + 1 / (M : ℝ)) * (M : ℝ) = (M : ℝ) + 1 := by field_simp
      rw [heq]
      exact le_of_lt hlt
    calc Real.log (((T : ℝ) / (d : ℝ)) / (M : ℝ))
        ≤ Real.log (1 + 1 / (M : ℝ)) :=
          Real.log_le_log (div_pos (div_pos hTpos hdpos) hMpos) hle2
      _ ≤ 1 / (M : ℝ) := log_one_add_inv_le_aux hMpos
      _ ≤ 1 := by
          rw [div_le_one hMpos]
          exact_mod_cast hM1
  have hnonpos : Real.log (M : ℝ) - Real.log ((T : ℝ) / (d : ℝ)) ≤ 0 :=
    sub_nonpos.mpr hlogle
  rw [abs_of_nonpos hnonpos]
  linarith [h1]

/-- An `Icc` sum equals the corresponding truncated-set filtered sum,
    when the summand vanishes off the truncated set. -/
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
theorem sum_mertensWeight_eq_aux {T : ℕ} (_hT : 1 ≤ T) :
    (∑ D ∈ Finset.range (T + 1), mertensWeight_aux D)
      = ∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * harmLogPow_aux 0 (T / d) := by
  have hrange : (∑ D ∈ Finset.range (T + 1), mertensWeight_aux D)
      = ∑ n ∈ Finset.Icc 1 T, mertensWeight_aux n := by
    have h1 : (∑ D ∈ Finset.range (T + 1), mertensWeight_aux D)
        = ∑ k ∈ Finset.range T, mertensWeight_aux (k + 1) := by
      rw [Finset.sum_range_succ', mertensWeight_zero_aux]
      simp
    have h2 : (∑ n ∈ Finset.Icc 1 T, mertensWeight_aux n)
        = ∑ k ∈ Finset.range T, mertensWeight_aux (k + 1) := by
      have hIcc : Finset.Icc 1 T = Finset.Ico 1 (T + 1) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro k _
      rw [add_comm]
    rw [h1, h2]
  have hstep : ∀ n ∈ Finset.Icc 1 T, mertensWeight_aux n
      = ∑ x ∈ n.divisorsAntidiagonal, convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have e1 : mertensWeight_aux n = convB_aux n / (n : ℝ) := by
      show mertensWeight_aux n = (n : ℝ) * mertensWeight_aux n / (n : ℝ)
      symm
      rw [div_eq_iff hn0']
      ring
    have e2 : convB_aux n / (n : ℝ) = divSumC_aux n / (n : ℝ) := by rw [convB_eq_divSumC_aux]
    have e3 : divSumC_aux n / (n : ℝ)
        = ∑ x ∈ n.divisorsAntidiagonal, convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ) := by
      show (∑ d ∈ n.divisors, convC_aux d) / (n : ℝ) = _
      rw [Finset.sum_div]
      have hmap : (∑ x ∈ n.divisorsAntidiagonal, convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ))
          = ∑ d ∈ n.divisors, convC_aux d / (n : ℝ) := by
        have hterm : (∑ x ∈ n.divisorsAntidiagonal, convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ))
            = ∑ x ∈ n.divisorsAntidiagonal, convC_aux x.1 / (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxx : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
          rw [hxx]
        rw [hterm, ← Nat.map_div_right_divisors, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro d _
        rfl
      rw [hmap]
    rw [e1, e2, e3]
  have hdisj : ((Finset.Icc 1 T : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun n => n.divisorsAntidiagonal) := by
    intro x _hx y _hy hne
    show Disjoint x.divisorsAntidiagonal y.divisorsAntidiagonal
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ hab hab'
    have h1 := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have h2 := (Nat.mem_divisorsAntidiagonal.mp hab').1
    exact hne (by omega)
  have hdisj2 : ((Finset.Icc 1 T : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun d => ({d} : Finset ℕ) ×ˢ Finset.Icc 1 (T / d)) := by
    intro x _hx y _hy hne
    show Disjoint (({x} : Finset ℕ) ×ˢ Finset.Icc 1 (T / x)) (({y} : Finset ℕ) ×ˢ Finset.Icc 1 (T / y))
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ hab hab'
    have h1 : a = x := by
      have h := (Finset.mem_product.mp hab).1
      simpa using h
    have h2 : a = y := by
      have h := (Finset.mem_product.mp hab').1
      simpa using h
    exact hne (by omega)
  have hsets : (Finset.Icc 1 T).biUnion (fun d => ({d} : Finset ℕ) ×ˢ Finset.Icc 1 (T / d))
      = (Finset.Icc 1 T).biUnion (fun n => n.divisorsAntidiagonal) := by
    ext ⟨d, m⟩
    simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_singleton, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨d', ⟨hd'1, hd'T⟩, hd, hm1, hmle⟩
      have hd'0 : 0 < d' := by omega
      have hd1 : 1 ≤ d := by omega
      have hdm : d * m ≤ T := by
        have hle := (nat_le_div_iff_mul_le_aux hd'0).mp hmle
        have heq : d * m = m * d' := by rw [hd]; ring
        omega
      have hdm1 : 1 ≤ d * m := by
        have h := mul_le_mul hd1 hm1
        simpa using h
      exact ⟨d * m, ⟨hdm1, hdm⟩, rfl, by omega⟩
    · rintro ⟨n, ⟨hn1, hnT⟩, hdm, hn0⟩
      have hd1 : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · subst hd0
          rw [Nat.zero_mul] at hdm
          omega
        · omega
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          rw [Nat.mul_zero] at hdm
          omega
        · omega
      have hdT : d ≤ T := by
        have hle : d ≤ d * m := by
          have h := mul_le_mul (le_refl d) hm1 (Nat.zero_le _) (Nat.zero_le _)
          simpa using h
        omega
      have hmle : m ≤ T / d := by
        apply (nat_le_div_iff_mul_le_aux (by omega : 0 < d)).mpr
        have heq : m * d = d * m := by ring
        omega
      exact ⟨d, ⟨hd1, hdT⟩, rfl, hm1, hmle⟩
  calc (∑ D ∈ Finset.range (T + 1), mertensWeight_aux D)
      = ∑ n ∈ Finset.Icc 1 T, mertensWeight_aux n := hrange
    _ = ∑ n ∈ Finset.Icc 1 T, ∑ x ∈ n.divisorsAntidiagonal,
          convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hstep n hn
    _ = ∑ x ∈ (Finset.Icc 1 T).biUnion (fun n => n.divisorsAntidiagonal),
          convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ) := by
        rw [Finset.sum_biUnion hdisj]
    _ = ∑ x ∈ (Finset.Icc 1 T).biUnion (fun d => ({d} : Finset ℕ) ×ˢ Finset.Icc 1 (T / d)),
          convC_aux x.1 / ((x.1 * x.2 : ℕ) : ℝ) := by
        rw [hsets]
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ m ∈ Finset.Icc 1 (T / d),
          convC_aux d / ((d * m : ℕ) : ℝ) := by
        rw [Finset.sum_biUnion hdisj2]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_product, Finset.sum_singleton]
    _ = ∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * harmLogPow_aux 0 (T / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hterm : ∀ m ∈ Finset.Icc 1 (T / d),
            convC_aux d / ((d * m : ℕ) : ℝ) = (convC_aux d / (d : ℝ)) * (1 / (m : ℝ)) := by
          intro m hm
          rw [Nat.cast_mul, div_mul_div_comm, mul_one]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, harmLogPow_zero_aux]

/-- The tail bound: the signed `Icc` sum differs from `1` by at most `24 e² / log T`. -/
theorem abs_A_sub_one_le_aux {T : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hsum1 : ∑ d ∈ truncSet_aux S, wSigned_aux d = 1)
    (hf : ∀ d ∈ Finset.Icc 1 T, d ∉ truncSet_aux S → wSigned_aux d = 0)
    (hT : 2 ≤ T) :
    abs ((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1)
      ≤ 24 * Real.exp 2 / Real.log (T : ℝ) := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hlogT : (0 : ℝ) < Real.log (T : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hsplit : (∑ d ∈ truncSet_aux S, wSigned_aux d)
      = (∑ d ∈ (truncSet_aux S).filter (fun d => d ≤ T), wSigned_aux d)
        + ∑ d ∈ (truncSet_aux S).filter (fun d => ¬ d ≤ T), wSigned_aux d :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hIcc : (∑ d ∈ Finset.Icc 1 T, wSigned_aux d)
      = ∑ d ∈ (truncSet_aux S).filter (fun d => d ≤ T), wSigned_aux d :=
    sum_Icc_eq_filter_truncSet_aux hS2 _ hf
  have hA : (∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1
      = -(∑ d ∈ (truncSet_aux S).filter (fun d => ¬ d ≤ T), wSigned_aux d) := by
    rw [hIcc]
    linarith [hsplit, hsum1]
  rw [hA, abs_neg]
  calc abs (∑ d ∈ (truncSet_aux S).filter (fun d => ¬ d ≤ T), wSigned_aux d)
      ≤ ∑ d ∈ (truncSet_aux S).filter (fun d => ¬ d ≤ T), abs (wSigned_aux d) :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ (truncSet_aux S).filter (fun d => ¬ d ≤ T), wAbs_aux d := by
        apply Finset.sum_congr rfl
        intro d hd
        exact abs_wSigned_aux d
    _ ≤ (∑ d ∈ (truncSet_aux S).filter (fun d => ¬ d ≤ T), wAbs_aux d * Real.log (d : ℝ))
          / Real.log (T : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro d hd
        have hdS : d ∈ truncSet_aux S := (Finset.mem_filter.mp hd).1
        have hd1 : 1 ≤ d := ((mem_truncSet_aux hS2).mp hdS).1
        have hdgt : T < d := by
          have hnot := (Finset.mem_filter.mp hd).2
          omega
        have h1le : (1 : ℝ) ≤ Real.log (d : ℝ) / Real.log (T : ℝ) := by
          rw [le_div_iff₀ hlogT, one_mul]
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < T))
            (by exact_mod_cast (le_of_lt hdgt))
        calc wAbs_aux d = wAbs_aux d * 1 := by ring
          _ ≤ wAbs_aux d * (Real.log (d : ℝ) / Real.log (T : ℝ)) :=
              mul_le_mul_of_nonneg_left h1le (wAbs_nonneg_aux d)
          _ = wAbs_aux d * Real.log (d : ℝ) / Real.log (T : ℝ) := by rw [mul_div_assoc]
    _ ≤ (∑ d ∈ truncSet_aux S, wAbs_aux d * Real.log (d : ℝ)) / Real.log (T : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (le_of_lt hlogT))
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d hd _
        have hd1 : 1 ≤ d := ((mem_truncSet_aux hS2).mp hd).1
        exact mul_nonneg (wAbs_nonneg_aux d) (Real.log_nonneg (by exact_mod_cast hd1))
    _ ≤ 24 * Real.exp 2 / Real.log (T : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (le_of_lt hlogT))
        exact sum_truncSet_wAbs_log_le_aux hS

/-- The log-weighted `Icc` sum is at most `24 e²`. -/
theorem abs_B_le_aux {T : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hf : ∀ d ∈ Finset.Icc 1 T, d ∉ truncSet_aux S → wAbs_aux d * Real.log (d : ℝ) = 0)
    (_hT : 1 ≤ T) :
    abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))
      ≤ 24 * Real.exp 2 := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  calc abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 T, abs ((convC_aux d / (d : ℝ)) * Real.log (d : ℝ)) :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Finset.Icc 1 T, wAbs_aux d * Real.log (d : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hd1)), abs_convC_div_aux]
    _ = ∑ d ∈ (truncSet_aux S).filter (fun d => d ≤ T), wAbs_aux d * Real.log (d : ℝ) :=
        sum_Icc_eq_filter_truncSet_aux hS2 _ hf
    _ ≤ ∑ d ∈ truncSet_aux S, wAbs_aux d * Real.log (d : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d hd _
        have hd1 : 1 ≤ d := ((mem_truncSet_aux hS2).mp hd).1
        exact mul_nonneg (wAbs_nonneg_aux d) (Real.log_nonneg (by exact_mod_cast hd1))
    _ ≤ 24 * Real.exp 2 := sum_truncSet_wAbs_log_le_aux hS

/-- The harmonic-error sum is at most `3 e²`. -/
theorem abs_E_le_aux {T : ℕ} (hT : 1 ≤ T) :
    abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
        * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ))))
      ≤ 3 * Real.exp 2 := by
  have hε : ∀ d ∈ Finset.Icc 1 T,
      abs (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ))) ≤ 3 := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdT : d ≤ T := (Finset.mem_Icc.mp hd).2
    have h1 := harm_err_le_two_aux (T / d)
    have h2 := log_div_nat_err_aux T d hd1 hdT
    have h2' : abs (Real.log ((T / d : ℕ) : ℝ)
        - (Real.log (T : ℝ) - Real.log (d : ℝ))) ≤ 1 := by
      have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
      have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
      rw [← Real.log_div hTne hdne]
      exact h2
    have h3 : harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ))
        = (harmLogPow_aux 0 (T / d) - Real.log ((T / d : ℕ) : ℝ))
          + (Real.log ((T / d : ℕ) : ℝ) - (Real.log (T : ℝ) - Real.log (d : ℝ))) := by
      ring
    rw [h3]
    calc abs ((harmLogPow_aux 0 (T / d) - Real.log ((T / d : ℕ) : ℝ))
          + (Real.log ((T / d : ℕ) : ℝ) - (Real.log (T : ℝ) - Real.log (d : ℝ))))
        ≤ abs (harmLogPow_aux 0 (T / d) - Real.log ((T / d : ℕ) : ℝ))
          + abs (Real.log ((T / d : ℕ) : ℝ) - (Real.log (T : ℝ) - Real.log (d : ℝ))) :=
          abs_add_le _ _
      _ ≤ 2 + 1 := add_le_add h1 h2'
      _ = 3 := by norm_num
  calc abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
        * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ))))
      ≤ ∑ d ∈ Finset.Icc 1 T, abs ((convC_aux d / (d : ℝ))
          * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ)))) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 T, wAbs_aux d * 3 := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul, abs_convC_div_aux]
        exact mul_le_mul_of_nonneg_left (hε d hd) (wAbs_nonneg_aux d)
    _ = 3 * ∑ d ∈ Finset.Icc 1 T, wAbs_aux d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [mul_comm]
    _ ≤ 3 * Real.exp 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
        calc ∑ d ∈ Finset.Icc 1 T, wAbs_aux d ≤ ∑ d ∈ Finset.range (T + 1), wAbs_aux d := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro d hd
                rw [Finset.mem_range]
                exact lt_of_le_of_lt (Finset.mem_Icc.mp hd).2 (by omega)
              · intro d _ _
                exact wAbs_nonneg_aux d
          _ ≤ Real.exp 2 := sum_range_wAbs_le_exp_two_aux T

/-- Assembly for `T ≥ 2`: `|S₀(T) - log T| ≤ 51 e²`. -/
theorem mertensS0_bound_aux_aux {T : ℕ} (hT : 2 ≤ T) :
    abs ((∑ D ∈ Finset.range (T + 1), mertensWeight_aux D) - Real.log (T : ℝ))
      ≤ 51 * Real.exp 2 := by
  have hT1 : 1 ≤ T := by omega
  have hS : ∀ p ∈ (Finset.range (T + 1)).filter (fun p => p.Prime), p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsum1 : ∑ d ∈ truncSet_aux ((Finset.range (T + 1)).filter (fun p => p.Prime)),
      wSigned_aux d = 1 :=
    sum_truncSet_wSigned_eq_one_aux hS
  have hfA : ∀ d ∈ Finset.Icc 1 T,
      d ∉ truncSet_aux ((Finset.range (T + 1)).filter (fun p => p.Prime)) → wSigned_aux d = 0 := by
    intro d hdIcc hdnot
    have hdT' : d ∈ Finset.range (T + 1) := by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (Finset.mem_Icc.mp hdIcc).2 (by omega)
    have hconv : convC_aux d = 0 := by
      by_contra hc
      exact hdnot (mem_truncSet_of_convC_ne_zero_aux hdT' hc)
    show convC_aux d / (d : ℝ) = 0
    rw [hconv]
    simp
  have hfB : ∀ d ∈ Finset.Icc 1 T,
      d ∉ truncSet_aux ((Finset.range (T + 1)).filter (fun p => p.Prime))
        → wAbs_aux d * Real.log (d : ℝ) = 0 := by
    intro d hdIcc hdnot
    have hdT' : d ∈ Finset.range (T + 1) := by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (Finset.mem_Icc.mp hdIcc).2 (by omega)
    have hconv : convC_aux d = 0 := by
      by_contra hc
      exact hdnot (mem_truncSet_of_convC_ne_zero_aux hdT' hc)
    show abs (convC_aux d) / (d : ℝ) * Real.log (d : ℝ) = 0
    rw [hconv]
    simp
  have htail := abs_A_sub_one_le_aux hS hsum1 hfA hT
  have hB := abs_B_le_aux hS hfB hT1
  have hE := abs_E_le_aux hT1
  have hswap := sum_mertensWeight_eq_aux hT1
  have hdecomp : (∑ D ∈ Finset.range (T + 1), mertensWeight_aux D)
      = (∑ d ∈ Finset.Icc 1 T, convC_aux d / (d : ℝ)) * Real.log (T : ℝ)
        - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))
        + (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
            * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ)))) := by
    rw [hswap]
    have hper : ∀ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * harmLogPow_aux 0 (T / d)
        = (convC_aux d / (d : ℝ)) * (Real.log (T : ℝ) - Real.log (d : ℝ))
          + (convC_aux d / (d : ℝ))
            * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ))) := by
      intro d hd
      ring
    have hper2 : ∀ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * (Real.log (T : ℝ) - Real.log (d : ℝ))
        = (convC_aux d / (d : ℝ)) * Real.log (T : ℝ)
          - (convC_aux d / (d : ℝ)) * Real.log (d : ℝ) := by
      intro d hd
      ring
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib,
      Finset.sum_congr rfl hper2, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hAw : (∑ d ∈ Finset.Icc 1 T, convC_aux d / (d : ℝ))
      = ∑ d ∈ Finset.Icc 1 T, wSigned_aux d := by
    apply Finset.sum_congr rfl
    intro d hd
    rfl
  have hlogT : (0 : ℝ) ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT1)
  have hlogTne : Real.log (T : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < T)))
  have hcancel : 24 * Real.exp 2 / Real.log (T : ℝ) * Real.log (T : ℝ)
      = 24 * Real.exp 2 := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hlogTne, mul_one]
  rw [hdecomp, hAw]
  have heq : (∑ d ∈ Finset.Icc 1 T, wSigned_aux d) * Real.log (T : ℝ)
      - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))
      + (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
          * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ))))
      - Real.log (T : ℝ)
      = ((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ)
        - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))
        + (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
            * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ)))) := by
    ring
  rw [heq]
  calc abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ)
        - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))
        + (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
            * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ)))))
      ≤ abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ)
          - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)))
        + abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
            * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ)))) :=
        abs_add_le _ _
    _ ≤ (abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ))
          + abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)))
        + abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ))
            * (harmLogPow_aux 0 (T / d) - (Real.log (T : ℝ) - Real.log (d : ℝ)))) :=
        by
        have hsub : abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ)
            - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)))
            ≤ abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ))
            + abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)) := by
          calc abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ)
                - (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)))
              = abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ)
                + (-(∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)))) := by
                congr 1
            _ ≤ abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ))
                + abs (-(∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ))) :=
                abs_add_le _ _
            _ = abs (((∑ d ∈ Finset.Icc 1 T, wSigned_aux d) - 1) * Real.log (T : ℝ))
                + abs (∑ d ∈ Finset.Icc 1 T, (convC_aux d / (d : ℝ)) * Real.log (d : ℝ)) := by
                rw [abs_neg]
        exact add_le_add hsub (le_refl _)
    _ ≤ (24 * Real.exp 2 / Real.log (T : ℝ) * Real.log (T : ℝ) + 24 * Real.exp 2)
        + 3 * Real.exp 2 := by
        apply add_le_add
        · apply add_le_add
          · rw [abs_mul, abs_of_nonneg hlogT]
            exact mul_le_mul_of_nonneg_right htail hlogT
          · exact hB
        · exact hE
    _ = 51 * Real.exp 2 := by
        rw [hcancel]
        ring

/-- The unconditional `S₀` bound with explicit constant `C₀ = 500`. -/
theorem mertensS0_bound_aux : ∀ i : ℕ,
    abs ((∑ D ∈ Finset.range (i + 1), mertensWeight_aux D) - Real.log (i : ℝ)) ≤ 500 := by
  intro i
  by_cases h0 : i = 0
  · subst h0
    have hsum : (∑ D ∈ Finset.range (0 + 1), mertensWeight_aux D) = 0 := by
      rw [show (0 + 1 : ℕ) = 1 from rfl, Finset.sum_range_one, mertensWeight_zero_aux]
    rw [hsum]
    simp only [Nat.cast_zero, Real.log_zero]
    norm_num
  · by_cases h1 : i = 1
    · subst h1
      have hsum : (∑ D ∈ Finset.range (1 + 1), mertensWeight_aux D) = 1 := by
        rw [Finset.sum_range_succ, Finset.sum_range_one, mertensWeight_zero_aux,
          mertensWeight_one_aux]
        norm_num
      rw [hsum]
      simp only [Nat.cast_one, Real.log_one]
      norm_num
    · have hi : 2 ≤ i := by omega
      have h51 := mertensS0_bound_aux_aux hi
      have hexp2 : Real.exp 2 < 9 := by
        have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
        have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        rw [h2]
        nlinarith [h1, hpos]
      have h500 : 51 * Real.exp 2 ≤ 500 := by linarith [hexp2]
      exact le_trans h51 h500

/-- The unconditional Mertens bound for `hMono`'s one-variable input,
    with explicit constant `C₀ = 500`. -/
theorem mertensMuSqBound_aux (m T : ℕ) :
    abs (mertensMuSqSum_aux m T - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ (6 + 2 * 500) * (Real.log (T : ℝ)) ^ m := by
  exact mertensMuSqSum_bound_of_S0_aux m T 500 (by norm_num) mertensS0_bound_aux


theorem solution (m T : ℕ) :
    abs ((∑ D ∈ Finset.range (T + 1), (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
      / ((Nat.totient D : ℕ) : ℝ) else 0) * (Real.log (D : ℝ)) ^ m)
      - (Real.log (T : ℝ)) ^ (m + 1) / ((m : ℝ) + 1))
      ≤ (6 + 2 * 500) * (Real.log (T : ℝ)) ^ m := mertensMuSqBound_aux m T

