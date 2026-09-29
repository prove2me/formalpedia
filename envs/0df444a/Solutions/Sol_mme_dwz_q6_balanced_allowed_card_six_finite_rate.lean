-- Prove2me | solution 1 for mme_dwz_q6_balanced_allowed_card_six_finite_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:07:06.871514+00:00
-- url     : https://prove2.me/submissions/5577bb48-44c4-43d8-aa64-6ee25375ab54

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorems.Thm_mme_Ctensor_balanced_count_matching_sqrt_loss
import Theorems.Thm_mme_dwz_q6_balanced_rows_allowed_card_exact
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace MME.DWZBalancedFiniteRate

theorem six_rpow_eq_square_volume (d : ℕ) (tau : ℝ) :
    (((d : ℝ) ^ tau) ^ (6 : ℕ)) =
      (((d ^ 2) * (d ^ 2) * (d ^ 2) : ℕ) : ℝ) ^ tau := by
  rw [Real.rpow_pow_comm (Nat.cast_nonneg d) tau 6]
  congr 1
  push_cast
  ring

theorem balanced_binary_six_rate
    (tau C₀ : ℝ) (htau : 0 ≤ tau) (hC₀ : 0 ≤ C₀)
    (N W D R : ℕ)
    (hD : D = W * 6 ^ N)
    (hNR : N ≤ R)
    (hcount :
      (2 : ℝ) ^ (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (W : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt
            (Real.log (((W + 1 : ℕ) : ℝ))))) :
    (((Real.rpow 12 tau) ^ N) ^ (6 : ℕ)) *
        Real.exp (-(3 * tau * C₀) *
          Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
      (((D ^ 2) * (D ^ 2) * (D ^ 2) : ℕ) : ℝ) ^ tau := by
  have he : 0 ≤ 3 * tau := by positivity
  have hC : 0 ≤ 3 * tau * C₀ := by positivity
  have hextra :
      Real.exp (-100 * Real.sqrt
          (Real.log (((W + 1 : ℕ) : ℝ)))) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hsqrt : 0 ≤ Real.sqrt
        (Real.log (((W + 1 : ℕ) : ℝ))) := Real.sqrt_nonneg _
    nlinarith
  have hcount' :
      (2 : ℝ) ^ (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (W : ℝ) ^ 2 := by
    calc
      (2 : ℝ) ^ (2 * N) *
            Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ)))
          ≤ (W : ℝ) ^ 2 *
              Real.exp (-100 * Real.sqrt
                (Real.log (((W + 1 : ℕ) : ℝ)))) := hcount
      _ ≤ (W : ℝ) ^ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hextra (sq_nonneg (W : ℝ))
      _ = (W : ℝ) ^ 2 := by ring
  have hraised := Real.rpow_le_rpow
    (by positivity : 0 ≤
      (2 : ℝ) ^ (2 * N) *
        Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))))
    hcount' he
  have hsqrt :
      Real.sqrt (((N + 1 : ℕ) : ℝ)) ≤
        Real.sqrt (((R + 1 : ℕ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hNR 1
  have hexpScale :
      Real.exp (-(3 * tau * C₀) *
          Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
        Real.exp (-(3 * tau * C₀) *
          Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have htwo :
      (((Real.rpow 2 tau) ^ N) ^ (6 : ℕ)) *
          Real.exp (-(3 * tau * C₀) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((W : ℝ) ^ tau) ^ (6 : ℕ)) := by
    have hleft :
        ((2 : ℝ) ^ (2 * N) *
            Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ)))) ^
              (3 * tau) =
          (((Real.rpow 2 tau) ^ N) ^ (6 : ℕ)) *
            Real.exp (-(3 * tau * C₀) *
              Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
      rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le]
      congr 1
      · calc
          ((2 : ℝ) ^ (2 * N)) ^ (3 * tau) =
              Real.rpow 2 (((2 * N : ℕ) : ℝ) * (3 * tau)) := by
                exact (Real.rpow_natCast_mul
                  (by norm_num : (0 : ℝ) ≤ 2) (2 * N) (3 * tau)).symm
          _ = Real.rpow 2 ((tau * (N : ℝ)) * (6 : ℝ)) := by
            congr 1
            push_cast
            ring
          _ = (Real.rpow 2 (tau * (N : ℝ))) ^ (6 : ℕ) := by
            exact Real.rpow_mul_natCast
              (by norm_num : (0 : ℝ) ≤ 2) (tau * (N : ℝ)) 6
          _ = ((Real.rpow 2 tau) ^ N) ^ (6 : ℕ) := by
            congr 1
            simpa only [Real.rpow_eq_pow] using
              Real.rpow_mul_natCast
                (by norm_num : (0 : ℝ) ≤ 2) tau N
      · calc
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ^
                (3 * tau) =
              Real.exp ((-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) *
                (3 * tau)) := by
                  exact (Real.exp_mul _ _).symm
          _ = Real.exp (-(3 * tau * C₀) *
                Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
            congr 1
            ring
    have hright :
        ((W : ℝ) ^ 2) ^ (3 * tau) =
          (((W : ℝ) ^ tau) ^ (6 : ℕ)) := by
      calc
        ((W : ℝ) ^ 2) ^ (3 * tau) =
            Real.rpow (W : ℝ) ((2 : ℝ) * (3 * tau)) := by
              exact (Real.rpow_natCast_mul
                (Nat.cast_nonneg W) 2 (3 * tau)).symm
        _ = Real.rpow (W : ℝ) (tau * (6 : ℝ)) := by
          congr 1
          ring
        _ = ((W : ℝ) ^ tau) ^ (6 : ℕ) := by
          exact Real.rpow_mul_natCast (Nat.cast_nonneg W) tau 6
    rw [← hleft, ← hright]
    exact hraised
  have htwoScale :
      (((Real.rpow 2 tau) ^ N) ^ (6 : ℕ)) *
          Real.exp (-(3 * tau * C₀) *
            Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
        (((W : ℝ) ^ tau) ^ (6 : ℕ)) := by
    calc
      (((Real.rpow 2 tau) ^ N) ^ (6 : ℕ)) *
            Real.exp (-(3 * tau * C₀) *
              Real.sqrt (((R + 1 : ℕ) : ℝ)))
          ≤ (((Real.rpow 2 tau) ^ N) ^ (6 : ℕ)) *
              Real.exp (-(3 * tau * C₀) *
                Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hexpScale (by positivity)
      _ ≤ (((W : ℝ) ^ tau) ^ (6 : ℕ)) := htwo
  have hsixNonneg :
      0 ≤ ((Real.rpow 6 tau) ^ N) ^ (6 : ℕ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right htwoScale hsixNonneg
  calc
    ((Real.rpow 12 tau ^ N) ^ (6 : ℕ)) *
          Real.exp (-(3 * tau * C₀) *
            Real.sqrt (((R + 1 : ℕ) : ℝ)))
        = ((((Real.rpow 2 tau) ^ N) ^ (6 : ℕ)) *
              Real.exp (-(3 * tau * C₀) *
                Real.sqrt (((R + 1 : ℕ) : ℝ)))) *
            (((Real.rpow 6 tau) ^ N) ^ (6 : ℕ)) := by
              rw [show Real.rpow 12 tau =
                Real.rpow 2 tau * Real.rpow 6 tau by
                  calc
                    Real.rpow 12 tau = Real.rpow (2 * 6) tau := by norm_num
                    _ = Real.rpow 2 tau * Real.rpow 6 tau :=
                      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
                        (by norm_num : (0 : ℝ) ≤ 6)]
              rw [mul_pow, mul_pow]
              ring
    _ ≤ (((W : ℝ) ^ tau) ^ (6 : ℕ)) *
          (((Real.rpow 6 tau) ^ N) ^ (6 : ℕ)) := hmul
    _ = ((((D : ℝ) ^ tau) ^ (6 : ℕ))) := by
      rw [hD]
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have h6 :
          Real.rpow 6 tau ^ N = Real.rpow ((6 : ℝ) ^ N) tau := by
        calc
          Real.rpow 6 tau ^ N = Real.rpow 6 (tau * (N : ℝ)) :=
            (Real.rpow_mul_natCast
              (by norm_num : (0 : ℝ) ≤ 6) tau N).symm
          _ = Real.rpow 6 ((N : ℝ) * tau) := by ring_nf
          _ = Real.rpow ((6 : ℝ) ^ N) tau :=
            Real.rpow_natCast_mul
              (by norm_num : (0 : ℝ) ≤ 6) N tau
      have h6' :
          Real.rpow 6 tau ^ N = (((6 : ℝ) ^ N) ^ tau) := by
        simpa only [Real.rpow_eq_pow] using h6
      rw [h6']
      ring
    _ = (((D ^ 2) * (D ^ 2) * (D ^ 2) : ℕ) : ℝ) ^ tau :=
      six_rpow_eq_square_volume D tau

end MME.DWZBalancedFiniteRate

open MME.DWZBalancedFiniteRate

theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
          let D := Nat.card
            {w : PowIndex
                (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s))
                (MME.DWZTable2Counts.component s * m) //
              componentWordAllowed s m w}
          (((componentBase tau s) ^
              (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            (((D ^ 2) * (D ^ 2) * (D ^ 2) : ℕ) : ℝ) ^ tau := by
  have htau₀ : 0 ≤ tau := by linarith
  obtain ⟨C₀, hC₀, hcount⟩ :=
    mme_Ctensor_balanced_count_matching_sqrt_loss 2 (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hcount
  let C : ℝ := 3 * tau * C₀
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop k₀] with m hm
  intro s hs
  let N : ℕ := MME.DWZTable2Counts.component s * m
  let k : ℕ := MME.DWZTable2Counts.split s 1 * m
  let W : ℕ := Nat.card
    {g : Fin N → Fin 2 //
      ∀ h, Fintype.card {r : Fin N // g r = h} = k}
  let D : ℕ := Nat.card
    {w : PowIndex
        (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s)) N //
      componentWordAllowed s m w}
  have hsplitpos : 0 < MME.DWZTable2Counts.split s 1 := by
    rcases hs with rfl | rfl | rfl | rfl <;> decide
  have hmk : m ≤ k := by
    simpa only [k, mul_comm] using
      Nat.le_mul_of_pos_right m hsplitpos
  have hklarge : k₀ ≤ k := hm.trans hmk
  have hbalance : MME.DWZTable2Counts.component s =
      2 * MME.DWZTable2Counts.split s 1 := by
    rcases hs with rfl | rfl | rfl | rfl <;> decide
  have hN : N = 2 * k := by
    dsimp only [N, k]
    rw [hbalance]
    ring
  have hcountk :
      (2 : ℝ) ^ (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (W : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt
            (Real.log (((W + 1 : ℕ) : ℝ)))) := by
    have hk := hk₀ k hklarge
    rw [← hN] at hk
    simpa only [W, Nat.cast_ofNat] using hk
  have hNR : N ≤ MME.DWZTable2Counts.scale * m := by
    have hcomponent : MME.DWZTable2Counts.component s ≤
        MME.DWZTable2Counts.scale := by
      rcases hs with rfl | rfl | rfl | rfl <;> decide
    exact Nat.mul_le_mul_right m hcomponent
  have hD : D = W * 6 ^ N := by
    have hcard := mme_dwz_q6_balanced_rows_allowed_card_exact
      m s hs
    simpa only [D, W, N, k] using hcard
  have hbase : componentBase tau s = Real.rpow 12 tau := by
    have hsnotle2 : ¬ s.val ≤ 2 := by
      rcases hs with rfl | rfl | rfl | rfl <;> decide
    have hsle8 : s.val ≤ 8 := by
      rcases hs with rfl | rfl | rfl | rfl <;> decide
    simp only [componentBase, hsnotle2, hsle8, if_false, if_true]
  have hrate := balanced_binary_six_rate tau C₀ htau₀ hC₀
    N W D (MME.DWZTable2Counts.scale * m) hD hNR hcountk
  simpa only [C, D, N, hbase] using hrate
