-- Prove2me | solution 1 for stepanov_system_dimension_inequality_nat
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T16:51:15.922106+00:00
-- url     : https://prove2.me/submissions/535f2376-8c75-4373-b079-2f3e396c2525

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
import Theorems.Thm_stepanov_system_constraint_count

section






lemma stepanov_monotone_in_J
    {J₁ J₂ D ℓ x C : ℝ}
    (hA : 2 * J₁ * D > ℓ * (J₁ + x) + C)
    (hD_nonneg : 0 ≤ 2 * D - ℓ)
    (hJmono : J₁ ≤ J₂) :
  2 * J₂ * D > ℓ * (J₂ + x) + C :=
by
  have hmono :
      2 * J₁ * D - ℓ * (J₁ + x) ≤ 2 * J₂ * D - ℓ * (J₂ + x) :=
    sub_nonneg.mp <| by
      have h : 0 ≤ (J₂ - J₁) * (2 * D - ℓ) :=
        mul_nonneg (sub_nonneg.mpr hJmono) hD_nonneg
      have :
          (2 * J₂ * D - ℓ * (J₂ + x)) -
            (2 * J₁ * D - ℓ * (J₁ + x)) =
            (J₂ - J₁) * (2 * D - ℓ) := by
        ring
      simpa [this] using h
  simpa [add_comm] using
    (lt_sub_iff_add_lt).1 <|
      lt_of_lt_of_le
        ((lt_sub_iff_add_lt).2 (by simpa [add_comm] using hA))
        hmono

lemma stepanov_twoD_sub_ell_pos
    (q m ℓ : ℕ) (hq6m : q > 6 * m) (hℓ : ℓ ≤ q / 3) :
  0 < 2 * (Int.ceil (((q : ℝ) - (m : ℝ)) / 2) : ℝ) - (ℓ : ℝ) :=
by
  have hm_lt_qdiv6 : (m : ℝ) < (q : ℝ) / 6 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < (6 : ℝ))).mpr <|
      by
        have h : (6 : ℝ) * (m : ℝ) < (q : ℝ) := by
          exact_mod_cast (by simpa [Nat.mul_comm] using hq6m : 6 * m < q)
        simpa [mul_comm] using h
  have hℓ_le_qdiv3 : (ℓ : ℝ) ≤ (q : ℝ) / 3 := by
    have h1 : (ℓ : ℝ) ≤ ((q / 3 : ℕ) : ℝ) := by exact_mod_cast hℓ
    have h2 : ((q / 3 : ℕ) : ℝ) ≤ (q : ℝ) / 3 := by
      simpa using (Nat.cast_div_le (α := ℝ) (m := q) (n := 3))
    exact le_trans h1 h2
  set x : ℝ := ((q : ℝ) - (m : ℝ)) / 2 with hx
  have h_lt : (ℓ : ℝ) < 2 * (Int.ceil x : ℝ) := by
    have h_ell_lt_qm : (ℓ : ℝ) < (q : ℝ) - (m : ℝ) := by
      have h : (q : ℝ) / 2 < (q : ℝ) - (m : ℝ) - (ℓ : ℝ) := by
        nlinarith [hm_lt_qdiv6, hℓ_le_qdiv3]
      nlinarith [h]
    have h_qm_le : (q : ℝ) - (m : ℝ) ≤ 2 * (Int.ceil x : ℝ) := by
      have hx_two : (2 : ℝ) * x = (q : ℝ) - (m : ℝ) := by
        have : x + x = (q : ℝ) - (m : ℝ) := by simp [hx, add_halves]
        simpa [two_mul] using this
      have := (mul_le_mul_of_nonneg_left (Int.le_ceil x) (by norm_num) :
        (2 : ℝ) * x ≤ (2 : ℝ) * (Int.ceil x : ℝ))
      simpa [hx_two] using this
    exact lt_of_lt_of_le h_ell_lt_qm h_qm_le
  exact sub_pos.mpr (by simpa [hx] using h_lt)





























end



theorem solution
    (q m ℓ : ℕ)
    (hm_ge_two : 2 ≤ m) (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hℓ_pos : 0 < ℓ)
    (B : ℕ)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) +
        (Nat.ceil (((q : ℚ) - m) / 2) - 1) + k * (m - 1))) :
    let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
    2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B :=
by
  intro J
  -- basic integer setup
  set d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1 with hd
  have hB_le : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
    simpa [J, hd, add_comm, add_left_comm, add_assoc] using hB
  have hq6m_nat : 6 * m < q := by simpa [Nat.mul_comm] using hq6m
  have hq_pos_nat : 0 < q := lt_of_le_of_lt (Nat.zero_le (6 * m)) hq6m_nat
  have hm_lt_q : m < q :=
    lt_of_le_of_lt
      (by
        have h16 : (1 : ℕ) ≤ 6 := by decide
        have := Nat.mul_le_mul_right m h16
        simpa [Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this)
      hq6m_nat
  -- positivity of the expression defining J
  have hJ_expr_pos :
      0 < ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) := by
    have hℓ_posℚ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ_pos
    have h_half_pos : (0 : ℚ) < (ℓ : ℚ) / 2 :=
      div_pos hℓ_posℚ (by norm_num : (0 : ℚ) < 2)
    have hq_posℚ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
    have h_div_nonneg :
        (0 : ℚ) ≤ ((ℓ : ℚ) ^ 2 * (m : ℚ)) / (q : ℚ) :=
      div_nonneg
        (mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m)))
        (le_of_lt hq_posℚ)
    have h_add :
        (0 : ℚ) < (ℓ : ℚ) / 2 + ((ℓ : ℚ) ^ 2 * (m : ℚ)) / (q : ℚ) :=
      add_pos_of_pos_of_nonneg h_half_pos h_div_nonneg
    simpa [add_comm] using h_add
  have hJ_pos : 1 ≤ J :=
    (Nat.one_le_ceil_iff
      (a := ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))).2
      hJ_expr_pos
  -- apply constraint-count inequality and simplify its RHS a bit
  have hB_real_small :
      (B : ℝ) <
        (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
          (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
    (stepanov_system_constraint_count ℓ J d m q B
      hℓ_pos hm_ge_two hq6m_nat hl hd hJ_pos hB_le).2
  -- some simple arithmetic bounds
  have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Nat.zero_le ℓ)
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm_ge_two
  have hm1_nonneg : 0 ≤ (m : ℝ) - 1 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hm_pos)
    exact sub_nonneg.mpr hm1
  -- compare the quadratic term in ℓ with a simpler upper bound
  have hcoef_le :
      ((ℓ : ℝ) - 1) * ((m : ℝ) - 1) ≤ (ℓ : ℝ) * ((m : ℝ) - 1) := by
    have htmp : (ℓ : ℝ) - 1 ≤ (ℓ : ℝ) :=
      sub_le_self _ (show (0 : ℝ) ≤ 1 by norm_num)
    exact mul_le_mul_of_nonneg_right htmp hm1_nonneg
  have hcoef_div_le :
      (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 ≤
        (ℓ : ℝ) * ((m : ℝ) - 1) / 2 := by
    have h_half_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_right hcoef_le h_half_nonneg
    simpa [div_eq_mul_inv, mul_assoc] using this
  have hterm_mul_le :
      (ℓ : ℝ) * ((((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) ≤
        (ℓ : ℝ) * (((ℓ : ℝ) * ((m : ℝ) - 1)) / 2) :=
    mul_le_mul_of_nonneg_left hcoef_div_le hℓ_nonneg
  have h_end :
      (ℓ : ℝ) * (((ℓ : ℝ) * ((m : ℝ) - 1)) / 2) =
        (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 := by
    simp [pow_two, mul_assoc, div_eq_mul_inv]
  have h_constr_le_Bmax_J :
      (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2)
        ≤ (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 := by
    calc
      (ℓ : ℝ) *
            ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
              (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2)
          = (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
              (ℓ : ℝ) * ((((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
            ring
      _ ≤ (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) * ((m : ℝ) - 1)) / 2) :=
        add_le_add_right hterm_mul_le _
      _ = (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 := by
        simp [h_end]
  have hB_lt_Bmax_J :
      (B : ℝ) <
        (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
          (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 :=
    lt_of_lt_of_le hB_real_small h_constr_le_Bmax_J
  -- switch to a more convenient notation over ℝ
  set Jreal : ℝ :=
      (ℓ : ℝ) / 2 + ((ℓ : ℝ) ^ 2 * (m : ℝ)) / (q : ℝ) with hJreal_def
  set xR : ℝ := ((q : ℝ) - (m : ℝ)) / 2 with hxR_def
  set D : ℝ := (Int.ceil xR : ℝ) with hD_def
  set C : ℝ := (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 with hC_def
  -- nonnegativity of 2D − ℓ
  have hD_nonneg : 0 ≤ 2 * D - (ℓ : ℝ) := by
    have hpos := stepanov_twoD_sub_ell_pos q m ℓ hq6m hl
    have : 0 < 2 * (Int.ceil xR : ℝ) - (ℓ : ℝ) := by
      simpa [xR, hxR_def, D, hD_def] using hpos
    exact le_of_lt this
  -- relate Jreal and J (ceil over ℚ vs ℝ)
  set tQ : ℚ :=
      (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) with htQ_def
  have htQ_le_ceil : (tQ : ℚ) ≤ Nat.ceil tQ := Nat.le_ceil tQ
  have hJreal_le_J : Jreal ≤ (J : ℝ) := by
    have : (tQ : ℝ) ≤ (Nat.ceil tQ : ℝ) := by exact_mod_cast htQ_le_ceil
    simpa [Jreal, tQ, hJreal_def, htQ_def] using this
  -- define A_real and Bmax_real
  set A_real : ℝ := 2 * Jreal * D with hAreal_def
  set Bmax_real : ℝ :=
      (ℓ : ℝ) * (Jreal + xR) + C with hBmax_def
  -- lower bound on A_real
  have hA_ge : Jreal * ((q : ℝ) - (m : ℝ)) ≤ A_real := by
    have hx_le_ceil : xR ≤ (Int.ceil xR : ℝ) := Int.le_ceil xR
    have hJreal_nonneg : (0 : ℝ) ≤ Jreal := by
      have h1 : (0 : ℝ) ≤ (ℓ : ℝ) / 2 :=
        div_nonneg hℓ_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h2 :
          (0 : ℝ) ≤ ((ℓ : ℝ) ^ 2 * (m : ℝ)) / (q : ℝ) := by
        have hnum : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 * (m : ℝ) :=
          mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m))
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
        exact div_nonneg hnum (le_of_lt hq_pos)
      have := add_nonneg h1 h2
      simpa [Jreal, hJreal_def] using this
    have h2J_nonneg : (0 : ℝ) ≤ 2 * Jreal :=
      mul_nonneg (by norm_num) hJreal_nonneg
    have hmul :
        (2 * Jreal) * xR ≤
          (2 * Jreal) * (Int.ceil xR : ℝ) :=
      mul_le_mul_of_nonneg_left hx_le_ceil h2J_nonneg
    have hx_two : (2 : ℝ) * xR = (q : ℝ) - (m : ℝ) := by
      have : xR + xR = (q : ℝ) - (m : ℝ) := by
        simp [xR, add_halves]
      simpa [two_mul] using this
    have hA_left :
        (2 * Jreal) * xR = Jreal * ((q : ℝ) - (m : ℝ)) := by
      calc
        (2 * Jreal) * xR = Jreal * (2 * xR) := by ac_rfl
        _ = Jreal * ((q : ℝ) - (m : ℝ)) := by simp [hx_two]
    have hA_eq :
        (2 * Jreal) * (Int.ceil xR : ℝ) = A_real := by
      simp [A_real, hAreal_def, D]
    have hA_aux : (2 * Jreal) * xR ≤ A_real := by
      simpa [hA_eq] using hmul
    simpa [hA_left] using hA_aux
  -- key inequality Jreal*(q-m) > Bmax_real
  have hJ_gt_Bmax : Bmax_real < Jreal * ((q : ℝ) - (m : ℝ)) := by
    -- first rewrite the difference in a more symmetric way
    have hD_eq :
        Jreal * ((q : ℝ) - (m : ℝ)) - Bmax_real =
          (Jreal - (ℓ : ℝ) / 2) *
              ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      have :
          Jreal * ((q : ℝ) - (m : ℝ)) -
              ((ℓ : ℝ) * (Jreal + xR) +
                (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2) =
            (Jreal - (ℓ : ℝ) / 2) *
                ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
              (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
        have :
            Jreal * ((q : ℝ) - (m : ℝ)) -
                ((ℓ : ℝ) *
                    (Jreal + ((q : ℝ) - (m : ℝ)) / 2) +
                      (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2) =
              (Jreal - (ℓ : ℝ) / 2) *
                  ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
                (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
          ring_nf
        simpa [xR, hxR_def] using this
      simpa [Bmax_real, hBmax_def] using this
    have h_eqJ :
        Jreal - (ℓ : ℝ) / 2 =
          (ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ) := by
      simp [Jreal, sub_eq_add_neg, add_comm, add_assoc]
    have hJ_minus_pos : 0 < Jreal - (ℓ : ℝ) / 2 := by
      have hℓ_sq_pos : 0 < (ℓ : ℝ) ^ 2 := by
        have hℓ_pos' : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        have := pow_pos hℓ_pos' (2 : ℕ)
        simpa [pow_two] using this
      have hpos_num : 0 < (ℓ : ℝ) ^ 2 * (m : ℝ) :=
        mul_pos hℓ_sq_pos (by exact_mod_cast hm_pos)
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
      have : 0 < (ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ) :=
        div_pos hpos_num hq_pos
      simpa [h_eqJ] using this
    -- obtain that q/2 < q − m − ℓ
    have hq6m_real : (6 : ℝ) * (m : ℝ) < (q : ℝ) := by exact_mod_cast hq6m_nat
    have hm_lt_qdiv6 : (m : ℝ) < (q : ℝ) / 6 := by
      have h6pos : (0 : ℝ) < (6 : ℝ) := by norm_num
      have : (m : ℝ) * 6 < (q : ℝ) := by
        simpa [mul_comm] using hq6m_real
      exact (lt_div_iff₀ h6pos).mpr this
    have hℓ_le_qdiv3 : (ℓ : ℝ) ≤ (q : ℝ) / 3 := by
      have hℓ_le_nat : (ℓ : ℝ) ≤ ((q / 3 : ℕ) : ℝ) := by
        exact_mod_cast hl
      have hqdiv3_le : ((q / 3 : ℕ) : ℝ) ≤ (q : ℝ) / 3 := by
        simpa using (Nat.cast_div_le (α := ℝ) (m := q) (n := 3))
      exact le_trans hℓ_le_nat hqdiv3_le
    have h_qmℓ_gt :
        (q : ℝ) / 2 < (q : ℝ) - (m : ℝ) - (ℓ : ℝ) := by
      nlinarith [hm_lt_qdiv6, hℓ_le_qdiv3]
    -- compare two products using the previous inequality
    have h_prod_gt :
        (Jreal - (ℓ : ℝ) / 2) *
            ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) >
          (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2) :=
      mul_lt_mul_of_pos_left h_qmℓ_gt hJ_minus_pos
    have h_prod_eq :
        (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2) =
          (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      have hq_ne : (q : ℝ) ≠ 0 := by
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
        exact ne_of_gt hq_pos
      calc
        (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2)
            = ((ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ)) * ((q : ℝ) / 2) := by
              simp [h_eqJ]
        _ = (((ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ)) * (q : ℝ)) / 2 := by
              simp [div_eq_mul_inv, mul_assoc]
        _ = (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
              simp [div_eq_mul_inv, hq_ne, mul_assoc]
    have hmain :
        (Jreal - (ℓ : ℝ) / 2) *
            ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) >
          (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      simpa [h_prod_eq] using h_prod_gt
    have hD_pos :
        Jreal * ((q : ℝ) - (m : ℝ)) - Bmax_real > 0 := by
      have hD2_pos :
          (Jreal - (ℓ : ℝ) / 2) *
              ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 > 0 :=
        sub_pos.mpr hmain
      simpa [hD_eq] using hD2_pos
    exact sub_pos.mp hD_pos
  -- combine to get Bmax_real < A_real
  have hA_gt_Bmax : Bmax_real < A_real :=
    lt_of_lt_of_le hJ_gt_Bmax hA_ge
  -- monotonicity in J
  have hA_gt_Bmax_J :
      2 * (J : ℝ) * D >
        (ℓ : ℝ) * ((J : ℝ) + xR) + C :=
    stepanov_monotone_in_J (J₁ := Jreal) (J₂ := (J : ℝ)) (D := D)
      (ℓ := (ℓ : ℝ)) (x := xR) (C := C)
      (by
        have :
            (ℓ : ℝ) * (Jreal + xR) + C <
              2 * Jreal * D := by
          simpa [A_real, hAreal_def, Bmax_real, hBmax_def] using hA_gt_Bmax
        simpa using this)
      (by simpa [D, hD_def] using hD_nonneg)
      hJreal_le_J
  have hB_lt_A_real :
      (B : ℝ) < 2 * (J : ℝ) * D :=
    lt_of_lt_of_le hB_lt_Bmax_J (le_of_lt hA_gt_Bmax_J)
  -- convert the statement back to ℚ / ℕ
  set xQ : ℚ := ((q : ℚ) - m) / 2 with hxQ_def
  have hxQ_nonneg : 0 ≤ xQ := by
    have hsub_nonneg : 0 ≤ (q : ℚ) - m :=
      sub_nonneg.mpr (by exact_mod_cast (le_of_lt hm_lt_q))
    have htwo_nonneg : (0 : ℚ) ≤ 2 := by norm_num
    exact div_nonneg hsub_nonneg htwo_nonneg
  have h_natInt_expr :
      (Nat.ceil (((q : ℚ) - m) / 2) : ℝ) =
        (Int.ceil (((q : ℝ) - (m : ℝ)) / 2) : ℝ) := by
    have h1 : (Nat.ceil xQ : ℝ) = (Int.ceil xQ : ℝ) := by
      exact_mod_cast
        (Int.natCast_ceil_eq_ceil (R := ℚ) (a := xQ) hxQ_nonneg)
    have h2 : (Int.ceil xQ : ℝ) = (Int.ceil (xQ : ℝ) : ℝ) := by
      exact_mod_cast (Rat.ceil_cast (α := ℝ) xQ).symm
    have hx : (xQ : ℝ) = xR := by
      simp [xQ, xR]
    calc
      (Nat.ceil (((q : ℚ) - m) / 2) : ℝ)
          = (Nat.ceil xQ : ℝ) := rfl
      _ = (Int.ceil xQ : ℝ) := h1
      _ = (Int.ceil (xQ : ℝ) : ℝ) := h2
      _ = (Int.ceil xR : ℝ) := by simp [hx]
  have hA_nat_real :
      (2 * J * Nat.ceil (((q : ℚ) - m) / 2) : ℝ) =
        (2 * (J : ℝ)) * (Int.ceil xR : ℝ) := by
    simp [h_natInt_expr, xR]
  have hB_lt_A_nat_real :
      (B : ℝ) <
        (2 * J * Nat.ceil (((q : ℚ) - m) / 2) : ℝ) := by
    simpa [hA_nat_real, D, hD_def] using hB_lt_A_real
  exact
    (by
      exact_mod_cast hB_lt_A_nat_real :
        2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B)
