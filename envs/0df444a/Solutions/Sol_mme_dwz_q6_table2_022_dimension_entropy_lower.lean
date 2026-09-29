-- Prove2me | solution 1 for mme_dwz_q6_table2_022_dimension_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:45:07.271525+00:00
-- url     : https://prove2.me/submissions/8c6cea26-75fd-4e9e-9742-a2bb647fce1c

import Mathlib.Tactic
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_q6_table2_022_202_prescribed_dimension_restriction

open scoped BigOperators
open MME MME.DWZSquare MME.DWZTable2Component022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

private theorem multinomial_three_split (L G : ℕ) :
    Nat.multinomial Finset.univ (![L, G, L] : Fin 3 → ℕ) =
      Nat.choose (2 * L + G) L * Nat.choose (L + G) L := by
  have hfirst := Nat.choose_mul_factorial_mul_factorial
    (show L ≤ 2 * L + G by omega)
  have hsecond := Nat.choose_mul_factorial_mul_factorial
    (show L ≤ L + G by omega)
  rw [show 2 * L + G - L = L + G by omega] at hfirst
  rw [show L + G - L = G by omega] at hsecond
  have hfactorial :
      (L.factorial * G.factorial * L.factorial) *
          (Nat.choose (2 * L + G) L * Nat.choose (L + G) L) =
        (2 * L + G).factorial := by
    calc
      (L.factorial * G.factorial * L.factorial) *
            (Nat.choose (2 * L + G) L * Nat.choose (L + G) L) =
          Nat.choose (2 * L + G) L * L.factorial *
            (Nat.choose (L + G) L * L.factorial * G.factorial) := by ring
      _ = Nat.choose (2 * L + G) L * L.factorial *
            (L + G).factorial := by rw [hsecond]
      _ = (2 * L + G).factorial := hfirst
  rw [Nat.multinomial_univ_three]
  rw [show L + G + L = 2 * L + G by omega]
  symm
  exact Nat.eq_div_of_mul_eq_right (by positivity) hfactorial

theorem solution (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let D := Nat.card (Restricted022Word 6 m L G)
    let profile : Fin 3 → ℝ := ![splitA, 1 - 2 * splitA, splitA]
    Real.exp
        ((m : ℝ) * Real.log 2 * mme_modern_entropyBits profile) *
        ((6 ^ (2 * G) : ℕ) : ℝ) ≤
      (6 * (((m + 1 : ℕ) : ℝ))) ^ 3 * (D : ℝ) := by
  dsimp only
  let w : Fin 3 → ℕ := ![3477403, 93045194, 3477403]
  have hW : 0 < ∑ i, w i := by
    norm_num [w, Fin.sum_univ_succ]
  have hLower :=
    mme_dwz_multinomial_entropy_polynomial_lower w t ht hW
  have hsum : ∑ i, w i = 100000000 := by
    norm_num [w, Fin.sum_univ_succ]
  have hprofile :
      (fun i ↦ (w i : ℝ) / (((∑ j, w j : ℕ) : ℝ))) =
        (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ) := by
    funext i
    fin_cases i <;> norm_num [w, splitA, hsum]
  rw [hprofile, hsum] at hLower
  have hm : table2Power022 t =
      2 * table2OuterCount022 t + table2MiddleCount022 t := by
    simp [table2Power022, table2OuterCount022, table2MiddleCount022]
    omega
  have hrem : table2Power022 t - table2OuterCount022 t =
      table2OuterCount022 t + table2MiddleCount022 t := by omega
  have hmulti :
      Nat.multinomial Finset.univ (fun i ↦ w i * t) =
        splitWordCount (table2Power022 t) (table2OuterCount022 t) := by
    have h := multinomial_three_split
      (table2OuterCount022 t) (table2MiddleCount022 t)
    rw [← hm] at h
    rw [splitWordCount, hrem]
    have hw :
        (fun i ↦ w i * t) =
          (![table2OuterCount022 t, table2MiddleCount022 t,
            table2OuterCount022 t] : Fin 3 → ℕ) := by
      funext i
      fin_cases i <;>
        simp [w, table2OuterCount022, table2MiddleCount022]
    rw [hw]
    exact h
  rw [hmulti] at hLower
  have hD :
      Nat.card
          (Restricted022Word 6 (table2Power022 t)
            (table2OuterCount022 t) (table2MiddleCount022 t)) =
        splitWordCount (table2Power022 t) (table2OuterCount022 t) *
          6 ^ (2 * table2MiddleCount022 t) := by
    have hinput :=
      mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
        (K := ℚ) 0 t ht
    dsimp only at hinput
    exact hinput.2.1
  have hLower' :
      Real.exp
          (((table2Power022 t : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ)) ≤
        (6 * ((((table2Power022 t + 1 : ℕ) : ℝ)))) ^ 3 *
          (splitWordCount (table2Power022 t)
            (table2OuterCount022 t) : ℝ) := by
    calc
      Real.exp
            (((table2Power022 t : ℕ) : ℝ) * Real.log 2 *
              mme_modern_entropyBits
                (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ)) =
          Real.exp
            ((t : ℝ) * ((100000000 : ℝ) * Real.log 2 *
              mme_modern_entropyBits
                (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ))) := by
        congr 1
        simp only [table2Power022, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ (6 * (((100000000 * t + 1 : ℕ) : ℝ))) ^
            Fintype.card (Fin 3) *
          (splitWordCount (table2Power022 t)
            (table2OuterCount022 t) : ℝ) := hLower
      _ = (6 * ((((table2Power022 t + 1 : ℕ) : ℝ)))) ^ 3 *
          (splitWordCount (table2Power022 t)
            (table2OuterCount022 t) : ℝ) := by
        simp only [table2Power022, Fintype.card_fin]
  calc
    Real.exp
          (((table2Power022 t : ℕ) : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ)) *
        ((6 ^ (2 * table2MiddleCount022 t) : ℕ) : ℝ)
        ≤ ((6 * ((((table2Power022 t + 1 : ℕ) : ℝ)))) ^ 3 *
            (splitWordCount (table2Power022 t)
              (table2OuterCount022 t) : ℝ)) *
          ((6 ^ (2 * table2MiddleCount022 t) : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hLower' (by positivity)
    _ = (6 * ((((table2Power022 t + 1 : ℕ) : ℝ)))) ^ 3 *
          (Nat.card
            (Restricted022Word 6 (table2Power022 t)
              (table2OuterCount022 t) (table2MiddleCount022 t)) : ℝ) := by
      rw [hD]
      push_cast
      ring
