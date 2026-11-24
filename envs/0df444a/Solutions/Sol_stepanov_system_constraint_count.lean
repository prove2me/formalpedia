-- Prove2me | solution 1 for stepanov_system_constraint_count
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T15:51:28.388143+00:00
-- url     : https://prove2.me/submissions/ec2b79f2-5b86-436c-844d-252075468426

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring




theorem solution
    (ℓ J d m q : ℕ) (B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : 6 * m < q)
    (_hℓ : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (_hJ : 1 ≤ J)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1))) :
    B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 ∧
    (B : ℝ) <
      (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
        (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
by
  have h_sum :
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
        ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
    have h_split :
        ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
          (∑ k ∈ Finset.range ℓ, (J + d)) +
            ∑ k ∈ Finset.range ℓ, k * (m - 1) := by
      calc
        ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
            ∑ k ∈ Finset.range ℓ, ((J + d) + k * (m - 1)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk; simp [add_assoc]
        _ = (∑ k ∈ Finset.range ℓ, (J + d)) +
              ∑ k ∈ Finset.range ℓ, k * (m - 1) := by
              simp [Finset.sum_add_distrib]
    have h_lin1 :
        ∑ k ∈ Finset.range ℓ, k * (m - 1) =
          (∑ k ∈ Finset.range ℓ, k) * (m - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Finset.sum_mul (s := Finset.range ℓ)
          (f := fun k : ℕ => k) (a := m - 1)).symm
    have h_sum_id :
        ∑ k ∈ Finset.range ℓ, k = ℓ * (ℓ - 1) / 2 :=
      Finset.sum_range_id ℓ
    have h_even : Even (ℓ * (ℓ - 1)) := Nat.even_mul_pred_self ℓ
    have h_mul_div :
        (ℓ * (ℓ - 1) / 2) * (m - 1) =
          ℓ * (ℓ - 1) * (m - 1) / 2 := by
      have hL :
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
            (ℓ * (ℓ - 1)) * (m - 1) := by
        have htmp :=
          Nat.two_mul_div_two_of_even (n := ℓ * (ℓ - 1)) h_even
        calc
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
              (2 * (ℓ * (ℓ - 1) / 2)) * (m - 1) := by
                ac_rfl
          _ = (ℓ * (ℓ - 1)) * (m - 1) := by
                simp [htmp]
      have hR :
          2 * (ℓ * (ℓ - 1) * (m - 1) / 2) =
            ℓ * (ℓ - 1) * (m - 1) :=
        Nat.two_mul_div_two_of_even
          (n := ℓ * (ℓ - 1) * (m - 1)) (h_even.mul_right (m - 1))
      have h_eq0 :
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
            2 * (ℓ * (ℓ - 1) * (m - 1) / 2) := by
        calc
          2 * ((ℓ * (ℓ - 1) / 2) * (m - 1)) =
              (ℓ * (ℓ - 1)) * (m - 1) := hL
          _ = 2 * (ℓ * (ℓ - 1) * (m - 1) / 2) := by
                simp [hR]
      have h_eq :
          ((ℓ * (ℓ - 1) / 2) * (m - 1)) * 2 =
            (ℓ * (ℓ - 1) * (m - 1) / 2) * 2 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq0
      have hne : (2 : ℕ) ≠ 0 := by decide
      exact mul_right_cancel₀ hne h_eq
    calc
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
          (∑ k ∈ Finset.range ℓ, (J + d)) +
            ∑ k ∈ Finset.range ℓ, k * (m - 1) := h_split
      _ = ℓ * (J + d) + (ℓ * (ℓ - 1) / 2) * (m - 1) := by
        simp [Finset.sum_const, Finset.card_range, h_lin1, h_sum_id]
      _ = ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
        calc
          ℓ * (J + d) + (ℓ * (ℓ - 1) / 2) * (m - 1)
              = ℓ * J + ℓ * d + (ℓ * (ℓ - 1) / 2) * (m - 1) := by
                ring
          _ = ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
                simp [h_mul_div]
  have hB_nat :
      B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
    simpa [h_sum] using hB
  have hB_real_le :
      (B : ℝ) ≤
        ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hB_nat
  have hx_pos : (0 : ℚ) < ((q : ℚ) - m) / 2 := by
    have hm_lt_q : m < q := by
      have hm_le_6m : m ≤ 6 * m := by
        simpa [Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_right m (show (1 : ℕ) ≤ 6 from by decide)
      exact lt_of_le_of_lt hm_le_6m hq6m
    have : (m : ℚ) < (q : ℚ) := by exact_mod_cast hm_lt_q
    exact div_pos (sub_pos.mpr this) (by norm_num)
  have hd_lt_rat : (d : ℚ) < ((q : ℚ) - m) / 2 :=
    Nat.lt_ceil.mp <| Nat.lt_of_le_pred (Nat.ceil_pos.mpr hx_pos) (by simp [hd])
  have hd_lt_real : (d : ℝ) < ((q : ℝ) - (m : ℝ)) / 2 := by
    exact_mod_cast hd_lt_rat
  have hEd_lt :
      (ℓ : ℝ) * (d : ℝ) <
        (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) :=
    mul_lt_mul_of_pos_left hd_lt_real (by exact_mod_cast hℓ_pos)
  have hS_cast :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) =
        (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          ((ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) := by
    simp [Nat.cast_add, Nat.cast_mul, add_assoc]
  have h_div_le :
      ((ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) ≤
        ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 := by
    simpa [Nat.cast_mul, mul_assoc, div_eq_mul_inv] using
      (Nat.cast_div_le (α := ℝ)
        (m := ℓ * (ℓ - 1) * (m - 1)) (n := 2))
  have hℓ_sub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    have hℓ_ge1 : 1 ≤ ℓ := Nat.succ_le_of_lt hℓ_pos
    simpa using (Nat.cast_sub (R := ℝ) hℓ_ge1)
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm_ge1 : 1 ≤ m :=
      le_trans (show (1 : ℕ) ≤ 2 by decide) hm_ge_two
    simpa using (Nat.cast_sub (R := ℝ) hm_ge1)
  have hCf_eq :
      ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 =
        (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    simp [hℓ_sub, hm_sub, mul_assoc]
  have hS_le_target1 :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) ≤
        (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    have h' :=
      add_le_add_left
        (add_le_add_left h_div_le ((ℓ : ℝ) * (d : ℝ)))
        ((ℓ : ℝ) * (J : ℝ))
    simpa [hS_cast, hCf_eq, add_assoc, add_comm, add_left_comm] using h'
  have hAEC_lt :
      (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 <
        (ℓ : ℝ) * (J : ℝ) +
          (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    exact
      add_lt_add_left
        (add_lt_add_right hEd_lt ((ℓ : ℝ) * (J : ℝ))) _
  have hS_lt_target :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) <
        (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
    have h' :
        ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) <
          (ℓ : ℝ) * (J : ℝ) +
            (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 :=
      lt_of_le_of_lt hS_le_target1 hAEC_lt
    have h_target_eq :
        (ℓ : ℝ) * (J : ℝ) +
            (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 =
          (ℓ : ℝ) *
            ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
              (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
      ring
    simpa [h_target_eq] using h'
  have hB_lt :
      (B : ℝ) <
        (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
    lt_of_le_of_lt hB_real_le hS_lt_target
  exact ⟨hB_nat, hB_lt⟩
