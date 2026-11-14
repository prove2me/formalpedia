-- Prove2me | solution 2 for markov_brothers_integer_grid_v2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T19:28:56.172218+00:00
-- url     : https://prove2.me/submissions/4bbd2a38-e587-4344-ad54-6ef20752d954

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators
open Finset Polynomial
set_option autoImplicit false

private def squareNode (i : ℕ) : ℝ := 2 * (i : ℝ)^2

private noncomputable def gridProduct (d : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 d, (1 - 1 / (2 * (j : ℝ)^2))

private theorem square_difference (i j : ℕ) (hji : j ≤ i) :
    (i : ℝ)^2 - (j : ℝ)^2 = ((i-j : ℕ) : ℝ) * ((i+j : ℕ) : ℝ) := by
  rw [Nat.cast_sub hji, Nat.cast_add]
  ring

private theorem square_product (i : ℕ) :
    (∏ j ∈ Finset.range i, ((i : ℝ)^2 - (j : ℝ)^2)) =
      (i.factorial : ℝ) * (i.ascFactorial i : ℝ) := by
  rw [Finset.prod_congr rfl (fun j hj =>
      square_difference i j (Nat.le_of_lt (Finset.mem_range.mp hj))), Finset.prod_mul_distrib]
  rw [← Nat.cast_prod, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
    ← Nat.ascFactorial_eq_prod_range, Nat.descFactorial_self]

private theorem factorial_ascent_top (i : ℕ) (hi : 1 ≤ i) :
    2 * i.factorial * i.ascFactorial i = (2*i).factorial := by
  rw [← Nat.mul_factorial_pred (by omega : i ≠ 0)]
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.factorial_mul_ascFactorial' i i (by omega)]
  rw [← Nat.mul_assoc, ← Nat.two_mul, Nat.mul_factorial_pred (by omega : 2*i ≠ 0)]

private theorem square_product_factorial (i : ℕ) (hi : 1 ≤ i) :
    2 * (∏ j ∈ Finset.range i, ((i : ℝ)^2 - (j : ℝ)^2)) = ((2*i).factorial : ℝ) := by
  simpa only [square_product, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    congrArg (fun n : ℕ => (n : ℝ)) (factorial_ascent_top i hi)

private theorem factorial_Icc (d : ℕ) :
    (∏ j ∈ Finset.Icc 1 d, (j : ℝ)) = (d.factorial : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simpa only [Nat.add_sub_cancel, Nat.add_comm, Nat.cast_prod] using
    congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_eq_prod_range_add_one d).symm

private theorem gridProduct_factorial (d : ℕ) :
    gridProduct d * ((d.factorial : ℝ)^2) =
      ∏ j ∈ Finset.Icc 1 d, ((j : ℝ)^2 - 1/2) := by
  rw [gridProduct, ← factorial_Icc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_Icc.mp hj).1)]

private theorem normalized_factor (i j : ℕ) :
    (Lagrange.basisDivisor (squareNode i) (squareNode j)).eval 1 =
      (1/2 - (j : ℝ)^2) / ((i : ℝ)^2 - (j : ℝ)^2) := by
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, squareNode]
  rw [← mul_sub, mul_inv_rev, div_eq_mul_inv]
  ring

private theorem square_half_nonneg (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ (j : ℝ)^2 - 1/2 := by
  nlinarith [sq_nonneg ((j : ℝ) - 1),
    show (1 : ℝ) ≤ (j : ℝ) from by exact_mod_cast hj]

private theorem normalized_factor_abs (i j : ℕ) (hij : i < j) :
    |(Lagrange.basisDivisor (squareNode i) (squareNode j)).eval 1| =
      ((j : ℝ)^2 - 1/2) / ((j : ℝ)^2 - (i : ℝ)^2) := by
  rw [normalized_factor, abs_div, abs_sub_comm (1/2) ((j : ℝ)^2),
    abs_sub_comm ((i : ℝ)^2) ((j : ℝ)^2)]
  rw [abs_of_nonneg (square_half_nonneg j (by omega)),
    abs_of_nonneg ((square_difference j i hij.le).symm ▸
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

private theorem abs_half_product (i : ℕ) (hi : 1 ≤ i) :
    (∏ j ∈ Finset.range i, |(1/2 : ℝ) - (j : ℝ)^2|) =
      (1/2 : ℝ) * ∏ j ∈ Finset.Icc 1 (i-1), ((j : ℝ)^2 - 1/2) := by
  rw [Finset.prod_range_eq_mul_Ico _ hi]
  norm_num
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hi]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [abs_sub_comm, abs_of_nonneg]
  exact square_half_nonneg j (Finset.mem_Ico.mp hj).1

private theorem square_weight_top (i : ℕ) (hi : 1 ≤ i) :
    |(Lagrange.basis (Finset.range (i+1)) squareNode i).eval 1| =
      gridProduct (i-1) * (((i-1).factorial : ℝ)^2) / ((2*i).factorial : ℝ) := by
  rw [Lagrange.basis, Finset.range_add_one,
    Finset.erase_insert Finset.notMem_range_self, Polynomial.eval_prod]
  simp_rw [normalized_factor]
  rw [Finset.prod_div_distrib, abs_div, Finset.abs_prod, Finset.abs_prod]
  rw [show (∏ j ∈ Finset.range i, |(i : ℝ)^2 - (j : ℝ)^2|) =
      ∏ j ∈ Finset.range i, ((i : ℝ)^2 - (j : ℝ)^2) from
    Finset.prod_congr rfl (fun j hj => abs_of_nonneg
      ((square_difference i j (Nat.le_of_lt (Finset.mem_range.mp hj))).symm ▸
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))]
  rw [abs_half_product i hi, ← gridProduct_factorial (i-1)]
  rw [← square_product_factorial i hi, div_mul_eq_div_mul_one_div]
  ring

private theorem square_weight_step (d i : ℕ) (hid : i ≤ d) :
    |(Lagrange.basis (Finset.range (d+2)) squareNode i).eval 1| =
      |(Lagrange.basis (Finset.range (d+1)) squareNode i).eval 1| *
        ((((d+1 : ℕ) : ℝ)^2 - 1/2) / (((d+1 : ℕ) : ℝ)^2 - (i : ℝ)^2)) := by
  rw [Lagrange.basis, Finset.range_add_one,
    Finset.erase_insert_of_ne (by omega : d+1 ≠ i),
    Finset.prod_insert (by simp [Finset.mem_erase, Finset.mem_range])]
  rw [← Lagrange.basis, Polynomial.eval_mul, abs_mul,
    normalized_factor_abs i (d+1) (by omega), mul_comm]

-- Explicit Lagrange weights at the quadratic integer nodes.
private theorem square_weight_eq (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    |(Lagrange.basis (Finset.range (d+1)) squareNode i).eval 1| =
      gridProduct d * ((d.factorial : ℝ)^2) /
        (((i : ℝ)^2 - 1/2) * ((d-i).factorial : ℝ) * ((d+i).factorial : ℝ)) := by
  induction d, hid using Nat.le_induction with
  | base =>
    rw [square_weight_top i hi, gridProduct_factorial, gridProduct_factorial,
      Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one,
      show i+i = 2*i from by omega]
    have hp : (∏ j ∈ Finset.Icc 1 i, ((j : ℝ)^2 - 1/2)) =
        (∏ j ∈ Finset.Icc 1 (i-1), ((j : ℝ)^2 - 1/2)) * ((i : ℝ)^2 - 1/2) := by
      simpa only [Nat.sub_add_cancel hi] using
        Finset.prod_Icc_succ_top (by omega : 1 ≤ (i-1)+1)
          (fun j : ℕ => (j : ℝ)^2 - 1/2)
    have hpos : (i : ℝ)^2 - 1/2 ≠ 0 := by
      nlinarith [sq_nonneg ((i : ℝ)-1),
        show (1 : ℝ) ≤ (i : ℝ) from by exact_mod_cast hi]
    rw [hp, mul_comm (∏ j ∈ Finset.Icc 1 (i-1), ((j : ℝ)^2 - 1/2)),
      mul_div_mul_left _ _ hpos]
  | succ d hid ih =>
    rw [square_weight_step d i hid, ih, gridProduct_factorial, gridProduct_factorial,
      Finset.prod_Icc_succ_top (by omega : 1 ≤ d+1)]
    rw [square_difference (d+1) i (by omega),
      show d+1-i = (d-i)+1 from by omega,
      show d+1+i = (d+i)+1 from by omega, Nat.factorial_succ, Nat.factorial_succ]
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring

private theorem reciprocal_step (x : ℝ) (hx : 1 ≤ x) :
    1 / ((x + 1)^2 - 1/2) ≤ 1/x - 1/(x+1) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  calc
    1 / ((x + 1)^2 - 1/2) ≤ 1 / (x * (x+1)) :=
      one_div_le_one_div_of_le (mul_pos hxpos (by linarith)) (by nlinarith)
    _ = 1/x - 1/(x+1) := by
      field_simp [ne_of_gt hxpos, ne_of_gt (show 0 < x+1 by linarith)]
      ring


private theorem reciprocal_sum_tail (d : ℕ) (hd : 3 ≤ d) :
    (∑ i ∈ Finset.Icc 1 d, (1 : ℝ) / ((i : ℝ)^2 - 1/2)) ≤ 977/357 - 1/(d:ℝ) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) from by decide]
  | succ d hd ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [reciprocal_step (d : ℝ) (by exact_mod_cast (show 1 ≤ d by omega))]

private theorem reciprocal_sum_bound (d : ℕ) :
    (∑ i ∈ Finset.Icc 1 d, (1 : ℝ) / ((i : ℝ)^2 - 1/2)) ≤ 977/357 := by
  by_cases hd : 3 ≤ d
  · exact (reciprocal_sum_tail d hd).trans (sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg d)))
  · interval_cases d <;> norm_num [Finset.sum_Icc_succ_top]

private theorem factor_pos (x : ℝ) (hx : 1 ≤ x) : 0 < 1 - 1/(2*x^2) := by
  have hden : 1 < 2*x^2 := by nlinarith [sq_nonneg (x-1)]
  exact sub_pos.mpr ((div_lt_one₀ (lt_trans (by norm_num) hden)).mpr hden)

private theorem gridProduct_pos (d : ℕ) : 0 < gridProduct d := by
  exact Finset.prod_pos fun j hj =>
    factor_pos (j : ℝ) (by exact_mod_cast (Finset.mem_Icc.mp hj).1)

private theorem product_factor_step (x : ℝ) (hx : 2 ≤ x) :
    ((2*x+2)/(2*x+1)) * (1 - 1/(2*(x+1)^2)) ≤ (2*x+4)/(2*x+3) := by
  have hdens : 0 < 2*x+1 ∧ 0 < 2*x+3 ∧ 0 < 2*(x+1)^2 :=
    ⟨by linarith, by linarith, by nlinarith [sq_nonneg x]⟩
  have heq : 1 - 1/(2*(x+1)^2) = (2*(x+1)^2-1)/(2*(x+1)^2) := by
    field_simp [hdens.2.2.ne']
  rw [heq, div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hdens.1 hdens.2.2) hdens.2.1).mpr
  nlinarith

private theorem gridProduct_upper (d : ℕ) (hd : 2 ≤ d) :
    gridProduct d ≤ (35/96 : ℝ) * ((2*(d:ℝ)+2)/(2*(d:ℝ)+1)) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [gridProduct, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from by decide]
  | succ d hd ih =>
    rw [gridProduct, Finset.prod_Icc_succ_top (by omega)]
    norm_num only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]
    refine (mul_le_mul_of_nonneg_right ih
      (factor_pos ((d:ℝ)+1) (by linarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d])).le).trans ?_
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (product_factor_step (d:ℝ) (by exact_mod_cast hd))
        (by norm_num : (0:ℝ) ≤ 35/96)

private theorem gridProduct_mul_lt (d : ℕ) (hd : 1 ≤ d) :
    gridProduct d * (d:ℝ) / ((d:ℝ)+1) < 35/96 := by
  by_cases hd2 : 2 ≤ d
  · have hupper : gridProduct d * (2*(d:ℝ)+1) ≤ (35/96 : ℝ) * (2*(d:ℝ)+2) :=
      (le_div_iff₀ (by linarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d])).mp
        (by simpa only [mul_div_assoc] using gridProduct_upper d hd2)
    apply (div_lt_iff₀ (by linarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d])).mpr
    nlinarith [gridProduct_pos d]
  · interval_cases d; norm_num [gridProduct, Finset.prod_Icc_succ_top]

private theorem factorial_pair_step (d i : ℕ) (hi : i < d) :
    (d-i).factorial * (d+i).factorial ≤ (d-(i+1)).factorial * (d+(i+1)).factorial := by
  rw [show d-i = d-(i+1)+1 from by omega, Nat.factorial_succ,
    show d+(i+1) = d+i+1 from by omega, Nat.factorial_succ]
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_right ((d-(i+1)).factorial * (d+i).factorial)
      (show d-(i+1)+1 ≤ d+i+1 from by omega)

private theorem factorial_pair_lower (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    (d-1).factorial * (d+1).factorial ≤ (d-i).factorial * (d+i).factorial := by
  induction i, hi using Nat.le_induction with
  | base => exact le_rfl
  | succ i hi ih =>
    exact (ih (by omega)).trans (factorial_pair_step d i (by omega))

private theorem factorial_ratio_nat (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    (d+1) * d.factorial^2 ≤ d * ((d-i).factorial * (d+i).factorial) := by
  calc
    (d+1) * d.factorial^2 = d * ((d-1).factorial * (d+1).factorial) := by
      rw [pow_two, Nat.factorial_succ, ← Nat.mul_factorial_pred (by omega : d ≠ 0)]
      ring
    _ ≤ d * ((d-i).factorial * (d+i).factorial) :=
      Nat.mul_le_mul_left d (factorial_pair_lower d i hi hid)

private theorem factorial_ratio_bound (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    ((d.factorial:ℝ)^2) / (((d-i).factorial:ℝ) * ((d+i).factorial:ℝ)) ≤
      (d:ℝ) / ((d:ℝ)+1) := by
  have hcast : ((d:ℝ)+1) * (d.factorial:ℝ)^2 ≤
      (d:ℝ) * (((d-i).factorial:ℝ) * ((d+i).factorial:ℝ)) := by
    exact_mod_cast factorial_ratio_nat d i hi hid
  apply (div_le_div_iff₀
    (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (Nat.cast_pos.mpr (Nat.factorial_pos _)))
    (by linarith [show (0:ℝ) ≤ (d:ℝ) from Nat.cast_nonneg d])).mpr
  simpa only [mul_comm] using hcast

private theorem square_weight_bound (d i : ℕ) (hi : 1 ≤ i) (hid : i ≤ d) :
    |(Lagrange.basis (Finset.range (d+1)) squareNode i).eval 1| ≤
      (35/96 : ℝ) / ((i : ℝ)^2 - 1/2) := by
  rw [square_weight_eq d i hi hid]
  calc
    _ = (gridProduct d * (((d.factorial : ℝ)^2) /
        (((d-i).factorial : ℝ) * ((d+i).factorial : ℝ)))) /
        ((i : ℝ)^2 - 1/2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (35/96 : ℝ) / ((i : ℝ)^2 - 1/2) := by
      apply div_le_div_of_nonneg_right _ (square_half_nonneg i hi)
      refine (mul_le_mul_of_nonneg_left (factorial_ratio_bound d i hi hid)
        (gridProduct_pos d).le).trans ?_
      simpa only [mul_div_assoc] using (gridProduct_mul_lt d (by omega)).le

private theorem squareNode_injective : Function.Injective squareNode := by
  intro i j hij
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) (by
    exact_mod_cast (mul_left_cancel₀ (by norm_num : (2:ℝ) ≠ 0) hij))

private theorem eval_one_bound_of_weights (d : ℕ) (Q : Polynomial ℝ)
    (hdeg : Q.natDegree ≤ d) (hzero : Q.eval 0 = 0)
    (hbound : ∀ t : ℕ, t ≤ 2*d^2 → |Q.eval (t : ℝ)| ≤ 1)
    (hweight : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      |(Lagrange.basis (Finset.range (d+1)) squareNode i).eval 1| ≤
        (35/96 : ℝ) / ((i : ℝ)^2 - 1/2))
    (hrecip : (∑ i ∈ Finset.Icc 1 d, (1 : ℝ) / ((i : ℝ)^2 - 1/2)) ≤ 977/357) :
    |Q.eval 1| ≤ 4885/4896 := by
  have hdegree : Q.degree < (Finset.range (d+1)).card := by
    simpa only [Finset.card_range, Nat.cast_withBot, Nat.succ_eq_add_one] using
      (Polynomial.degree_le_of_natDegree_le hdeg).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  have hinterp := Lagrange.eq_interpolate (f := Q) (s := Finset.range (d+1))
    (v := squareNode) squareNode_injective.injOn hdegree
  have heval := congrArg (Polynomial.eval (1:ℝ)) hinterp
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C] at heval
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos d), Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc] at heval
  simp only [show squareNode 0 = 0 from by norm_num [squareNode],
    hzero, zero_mul, zero_add] at heval
  have hnodes : ∀ i : ℕ, i ≤ d → |Q.eval (squareNode i)| ≤ 1 := fun i hi => by
    simpa only [squareNode, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      hbound (2*i^2) (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hi 2))
  calc
    |Q.eval 1| = |∑ i ∈ Finset.Icc 1 d,
        Q.eval (squareNode i) * (Lagrange.basis (Finset.range (d+1)) squareNode i).eval 1| :=
      congrArg abs heval
    _ ≤ ∑ i ∈ Finset.Icc 1 d,
        |Q.eval (squareNode i) * (Lagrange.basis (Finset.range (d+1)) squareNode i).eval 1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 d, (35/96 : ℝ) / ((i : ℝ)^2 - 1/2) := by
      apply Finset.sum_le_sum
      exact fun i hi => (abs_mul _ _).trans_le
        ((mul_le_mul_of_nonneg_right (hnodes i (Finset.mem_Icc.mp hi).2) (abs_nonneg _)).trans
          (by simpa only [one_mul] using
            hweight i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2))
    _ = (35/96 : ℝ) * (∑ i ∈ Finset.Icc 1 d, 1 / ((i : ℝ)^2 - 1/2)) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    _ ≤ (35/96 : ℝ) * (977/357) :=
      mul_le_mul_of_nonneg_left hrecip (by norm_num)
    _ = 4885/4896 := by norm_num

private theorem eval_one_bound (d : ℕ) (Q : Polynomial ℝ)
    (hdeg : Q.natDegree ≤ d) (hzero : Q.eval 0 = 0)
    (hbound : ∀ t : ℕ, t ≤ 2*d^2 → |Q.eval (t : ℝ)| ≤ 1) :
    |Q.eval 1| ≤ 4885/4896 := by
  exact eval_one_bound_of_weights d Q hdeg hzero hbound
    (fun i hi hid => square_weight_bound d i hi hid) (reciprocal_sum_bound d)

theorem solution
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_zero : Q.eval 0 = 0) (h_one : Q.eval 1 = 1)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) :
    b ≤ 2 * d^2 := by
  by_contra h
  have he := eval_one_bound d Q h_deg h_zero (fun t ht => h_bound t (by omega))
  norm_num [h_one] at he
