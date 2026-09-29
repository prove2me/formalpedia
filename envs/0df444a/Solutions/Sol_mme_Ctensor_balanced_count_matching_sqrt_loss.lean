-- Prove2me | solution 1 for mme_Ctensor_balanced_count_matching_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:37:58.724016+00:00
-- url     : https://prove2.me/submissions/78ab512c-3a85-4d44-b16e-c2e09d53f3bf

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finite.Card
import Theorems.Thm_mme_Ctensor_balanced_word_card_coarse_lower

open BigOperators Filter

set_option autoImplicit false

theorem solution
    (H : ℕ) (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        let W : ℕ :=
          Nat.card
            {w : Fin R → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
        ((H : ℝ) ^ (2 * R)) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          (W : ℝ) ^ 2 *
            Real.exp
              (-100 * Real.sqrt
                (Real.log (((W + 1 : ℕ) : ℝ)))) := by
  let C : ℝ := 14 * (H : ℝ) + 100 * (((H + 1 : ℕ) : ℝ))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  dsimp only
  let R : ℕ := H * m
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  let D : ℝ := (6 * (((m + 1 : ℕ) : ℝ))) ^ H
  let s : ℝ := Real.sqrt (((R + 1 : ℕ) : ℝ))
  let t : ℝ := Real.sqrt (Real.log (((W + 1 : ℕ) : ℝ)))
  have hmpos : 0 < m := by omega
  have hHone : 1 ≤ H := hH
  have hmR : m ≤ R := by
    dsimp [R]
    simpa [mul_comm] using Nat.le_mul_of_pos_right m hH
  have hRnonneg : 0 ≤ (R : ℝ) := by positivity
  have hRp1 : 0 ≤ ((R + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = ((R + 1 : ℕ) : ℝ) := by
    exact Real.sq_sqrt hRp1
  have hs_one : 1 ≤ s := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ s := by
        dsimp [s]
        apply Real.sqrt_le_sqrt
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hcoarse :
      (H : ℝ) ^ R ≤ D * (W : ℝ) := by
    dsimp [D, W, R]
    exact mme_Ctensor_balanced_word_card_coarse_lower H m hH hmpos
  have hWle : W ≤ H ^ R := by
    dsimp [W]
    calc
      Nat.card
            {w : Fin R → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
          ≤ Nat.card (Fin R → Fin H) :=
        Finite.card_subtype_le _
      _ = H ^ R := by simp
  have hHpowOne : 1 ≤ H ^ R := Nat.one_le_pow R H hH
  have hWcast : ((W + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ R := by
    exact_mod_cast (show W + 1 ≤ 2 * H ^ R by omega)
  have hlogUpper :
      Real.log (((W + 1 : ℕ) : ℝ)) ≤
        (((R + 1 : ℕ) : ℝ) * (((H + 1 : ℕ) : ℝ))) := by
    have hlogMono :=
      Real.log_le_log
        (by positivity : (0 : ℝ) < ((W + 1 : ℕ) : ℝ)) hWcast
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlogH : Real.log (H : ℝ) ≤ (H : ℝ) := by
      exact Real.log_le_self (by positivity)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero R (by exact_mod_cast hH.ne')),
      Real.log_pow] at hlogMono
    push_cast at hlogMono
    have hscaled := mul_le_mul_of_nonneg_left hlogH hRnonneg
    push_cast
    nlinarith
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht_le : t ≤ (((H + 1 : ℕ) : ℝ)) * s := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        Real.log (((W + 1 : ℕ) : ℝ))
            ≤ (((R + 1 : ℕ) : ℝ) * (((H + 1 : ℕ) : ℝ))) :=
          hlogUpper
        _ ≤ ((((H + 1 : ℕ) : ℝ)) * s) ^ 2 := by
          have hH1R : (1 : ℝ) ≤ (((H + 1 : ℕ) : ℝ)) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le H)
          have hH1nonneg : (0 : ℝ) ≤ (((H + 1 : ℕ) : ℝ)) := by positivity
          have hHsq : (((H + 1 : ℕ) : ℝ)) ≤
              (((H + 1 : ℕ) : ℝ)) ^ 2 := by
            have := mul_le_mul_of_nonneg_left hH1R hH1nonneg
            simpa [pow_two] using this
          calc
            (((R + 1 : ℕ) : ℝ) * (((H + 1 : ℕ) : ℝ)))
                ≤ (((R + 1 : ℕ) : ℝ) *
                    (((H + 1 : ℕ) : ℝ)) ^ 2) := by
                  gcongr
            _ = ((((H + 1 : ℕ) : ℝ)) * s) ^ 2 := by
              rw [mul_pow, hs_sq]
              ring
  have hm1nonneg : 0 ≤ ((m : ℝ) + 1) := by positivity
  have hm1pos : 0 < ((m : ℝ) + 1) := by positivity
  have hs_m : Real.sqrt ((m : ℝ) + 1) ≤ s := by
    dsimp [s]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hmR 1
  have hlogm :
      Real.log ((m : ℝ) + 1) ≤ 2 * Real.sqrt ((m : ℝ) + 1) := by
    have hsqrtPos : 0 < Real.sqrt ((m : ℝ) + 1) := by positivity
    have hbasic := Real.log_le_sub_one_of_pos hsqrtPos
    rw [Real.log_sqrt hm1nonneg] at hbasic
    nlinarith
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hlogD :
      Real.log D =
        (H : ℝ) *
          (Real.log 6 + Real.log ((m : ℝ) + 1)) := by
    dsimp [D]
    rw [Real.log_pow,
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity)]
    push_cast
    ring
  have hlogSix : Real.log (6 : ℝ) ≤ 5 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hlogD_le : Real.log D ≤ 7 * (H : ℝ) * s := by
    rw [hlogD]
    have hm_bound : Real.log ((m : ℝ) + 1) ≤ 2 * s :=
      hlogm.trans (mul_le_mul_of_nonneg_left hs_m (by norm_num))
    have hHnonneg : 0 ≤ (H : ℝ) := by positivity
    have hinside :
        Real.log 6 + Real.log ((m : ℝ) + 1) ≤ 7 * s := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hinside hHnonneg]
  have hexponent :
      2 * Real.log D + 100 * t ≤ C * s := by
    dsimp [C]
    have h1 := mul_le_mul_of_nonneg_left hlogD_le (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_left ht_le (by norm_num : (0 : ℝ) ≤ 100)
    calc
      2 * Real.log D + 100 * t
          ≤ 2 * (7 * (H : ℝ) * s) +
              100 * ((((H + 1 : ℕ) : ℝ)) * s) := add_le_add h1 h2
      _ = (14 * (H : ℝ) + 100 * (((H + 1 : ℕ) : ℝ))) * s := by ring
  have hDloss :
      D ^ 2 * Real.exp (-C * s) ≤ Real.exp (-100 * t) := by
    have hDrepr : D ^ 2 = Real.exp (2 * Real.log D) := by
      rw [show D = Real.exp (Real.log D) by exact (Real.exp_log hDpos).symm]
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hDrepr, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcount :
      (H : ℝ) ^ (2 * R) ≤ D ^ 2 * (W : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hcoarse 2
    calc
      (H : ℝ) ^ (2 * R) = ((H : ℝ) ^ R) ^ 2 := by
        rw [← pow_mul]
        simp [mul_comm]
      _ ≤ (D * (W : ℝ)) ^ 2 := hsq
      _ = D ^ 2 * (W : ℝ) ^ 2 := by rw [mul_pow]
  change
    (H : ℝ) ^ (2 * R) * Real.exp (-C * s) ≤
      (W : ℝ) ^ 2 * Real.exp (-100 * t)
  calc
    (H : ℝ) ^ (2 * R) * Real.exp (-C * s)
        ≤ (D ^ 2 * (W : ℝ) ^ 2) * Real.exp (-C * s) := by
          gcongr
    _ = (W : ℝ) ^ 2 * (D ^ 2 * Real.exp (-C * s)) := by ring
    _ ≤ (W : ℝ) ^ 2 * Real.exp (-100 * t) := by
      gcongr
