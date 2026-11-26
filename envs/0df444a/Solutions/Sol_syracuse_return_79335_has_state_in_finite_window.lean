-- Prove2me | solution 1 for syracuse_return_79335_has_state_in_finite_window
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:39:53.730217+00:00
-- url     : https://prove2.me/submissions/057f0788-4791-464c-8cda-04c7f3d1e1cf

import Theorems.Thm_syracuse_nontrivial_period_coordinates_at_1241513984
import Theorems.Thm_syracuse_cycle_three_consecutive_entries_budget
import Theorems.Thm_syracuse_no_cycle_below_1241513984
import Theorems.Thm_syracuse_periodic_reaches_one
import Mathlib.Dynamics.PeriodicPts.Defs

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open scoped BigOperators

private abbrev l2 : ℝ := 0.6931471805599453093
private abbrev u2 : ℝ := 0.6931471805599453095
private abbrev l3 : ℝ := 1.0986122886681096913
private abbrev u3 : ℝ := 1.0986122886681096915

set_option maxHeartbeats 0 in
set_option maxRecDepth 6000 in
private theorem log_bounds :
    l2 < Real.log 2 ∧ Real.log 2 < u2 ∧ l3 < Real.log 3 ∧ Real.log 3 < u3 := by
  have ha := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/3) (by norm_num) 40
  have hb := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/4) (by norm_num) 40
  rw [show 1 - (1:ℝ)/3 = ((3:ℝ)/2)⁻¹ by norm_num, Real.log_inv] at ha
  rw [show 1 - (1:ℝ)/4 = ((4:ℝ)/3)⁻¹ by norm_num, Real.log_inv] at hb
  norm_num [Finset.sum_range_succ] at ha hb
  obtain ⟨ha1,ha2⟩ := abs_le.mp ha
  obtain ⟨hb1,hb2⟩ := abs_le.mp hb
  have h2 : Real.log 2 = Real.log (3/2)+Real.log (4/3) := by
    rw [← Real.log_mul (by norm_num : (3:ℝ)/2 ≠ 0) (by norm_num : (4:ℝ)/3 ≠ 0)]
    norm_num
  have h3 : Real.log 3 = 2*Real.log (3/2)+Real.log (4/3) := by
    rw [show (3:ℝ) = ((3:ℝ)/2)^2*((4:ℝ)/3) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  unfold l2 u2 l3 u3
  constructor
  · linarith only [ha1,ha2,hb1,hb2,h2]
  constructor
  · linarith only [ha1,ha2,hb1,hb2,h2]
  constructor
  · linarith only [ha1,ha2,hb1,hb2,h3]
  · linarith only [ha1,ha2,hb1,hb2,h3]

private theorem step_log_bound (x : ℝ) (hx : 0 < x) :
    Real.log (3*x+1) ≤ Real.log 3 + Real.log x + 1/(3*x) := by
  have h3x : 0 < (3:ℝ)*x := by positivity
  have hs : 0 < 1+1/(3*x) := by positivity
  have he : 3*x+1 = (3*x)*(1+1/(3*x)) := by field_simp [hx.ne']
  have h := Real.log_le_sub_one_of_pos hs
  rw [he,Real.log_mul h3x.ne' hs.ne',Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hx.ne']
  linarith only [h]

private theorem triple_period_log_bound (m p : ℕ)
    (hcycle : syracuseStep^[p] m = m) (hbase : ∀ i : ℕ, 6150000000 ≤ syracuseStep^[i] m) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    (3:ℝ)*(K:ℝ)*Real.log 2 ≤ (p:ℝ)*
      (3*Real.log 3+1/(3*6150000000)+1/(3*6918750000)+1/(3*9225000000)) := by
  intro K
  let A : ℝ := 10598219087405485781316881250001
  let D : ℝ := 392526632812500000000000000000
  have haPos : 0 < A := by norm_num [A]
  have hdPos : 0 < D := by norm_num [D]
  have ha : Real.log A =
      Real.log (3*6150000000+1) + Real.log (3*6918750000+1) + Real.log (3*9225000000+1) := by
    rw [show A = ((3*6150000000+1)*(3*6918750000+1))*(3*9225000000+1) by norm_num [A],
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have hd : Real.log D =
      Real.log 6150000000 + Real.log 6918750000 + Real.log 9225000000 := by
    rw [show D = ((6150000000:ℝ)*6918750000)*9225000000 by norm_num [D],
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  let R : ℝ := 1/(3*6150000000)+1/(3*6918750000)+1/(3*9225000000)
  have hA : Real.log A ≤ Real.log D + (3*Real.log 3+R) := by
    rw [ha,hd]
    have h1 := step_log_bound 6150000000 (by norm_num)
    have h2 := step_log_bound 6918750000 (by norm_num)
    have h3 := step_log_bound 9225000000 (by norm_num)
    dsimp only [R]
    linarith only [h1,h2,h3]
  have hbudget := syracuse_cycle_three_consecutive_entries_budget m p 768750000 (by decide)
    hcycle hbase
  change 2^(3*K)*392526632812500000000000000000^p ≤ 10598219087405485781316881250001^p at hbudget
  have hcast := (Nat.cast_le (α := ℝ)).2 hbudget
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hcast
  change (2:ℝ)^(3*K)*D^p ≤ A^p at hcast
  have hl := Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by positivity : (2:ℝ)^(3*K) ≠ 0) (by positivity : D^p ≠ 0),
    Real.log_pow, Real.log_pow, Real.log_pow] at hl
  have hmul : (p:ℝ)*Real.log A ≤ (p:ℝ)*(Real.log D + (3*Real.log 3+R)) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  push_cast at hl
  have hR : 3*Real.log 3+1/(3*6150000000)+1/(3*6918750000)+1/(3*9225000000) =
      3*Real.log 3+R := by dsimp [R]; ring
  rw [hR]
  linarith only [hl,hmul]

private theorem first_coordinate_unique (p a b : ℕ)
    (hp : p = 79335) (ha : 0 < a) (hb : 0 < b)
    (he : p = 31867*a+47468*b) : a=1 ∧ b=1 := by
  constructor
  · by_contra hn
    have ha2 : 2 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne ha (Ne.symm hn))
    have hl : 31867*2+47468*1 ≤ 31867*a+47468*b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha2) (Nat.mul_le_mul_left _ hb)
    rw [← he,hp] at hl
    norm_num at hl
  · by_contra hn
    have hb2 : 2 ≤ b := Nat.succ_le_of_lt (lt_of_le_of_ne hb (Ne.symm hn))
    have hl : 31867*1+47468*2 ≤ 31867*a+47468*b :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb2)
    rw [← he,hp] at hl
    norm_num at hl

private theorem finite_window (m p : ℕ) (hm : 0 < m) (hp : p = 79335)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    ∃ i < p, 1241513984 ≤ syracuseStep^[i] m ∧ syracuseStep^[i] m < 6150000000 := by
  have hpPos : 0 < p := by omega
  let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
  have hK : K = 125743 := by
    obtain ⟨_,a,b,ha,hb,hPeriod,hValue⟩ :=
      syracuse_nontrivial_period_coordinates_at_1241513984 m p hm hpPos hcycle hne
    obtain ⟨ha1,hb1⟩ := first_coordinate_unique p a b hp ha hb hPeriod
    change K = _ at hValue
    rw [hValue,ha1,hb1]
  have hlow : ∃ i, syracuseStep^[i] m < 6150000000 := by
    by_contra hex
    have hbase (i : ℕ) : 6150000000 ≤ syracuseStep^[i] m :=
      Nat.le_of_not_gt (fun hi => hex ⟨i,hi⟩)
    let R : ℝ := 1/(3*6150000000)+1/(3*6918750000)+1/(3*9225000000)
    have hh : (3:ℝ)*(K:ℝ)*Real.log 2 ≤ (p:ℝ)*(3*Real.log 3+R) := by
      have h := triple_period_log_bound m p hcycle hbase
      dsimp only [R]
      linarith only [h]
    rw [hK,hp] at hh
    obtain ⟨h2l,_,_,h3u⟩ := log_bounds
    have hUp : (79335:ℝ)*(3*Real.log 3+R) < (3*125743)*Real.log 2 := calc
      _ ≤ (79335:ℝ)*(3*u3+R) := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left h3u.le (by norm_num)) le_rfl) (by norm_num)
      _ < (3*125743)*l2 := by norm_num [R,u3,l2]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2l.le (by norm_num)
    exact (not_lt_of_ge hh) hUp
  obtain ⟨i,hi⟩ := hlow
  let j := i % p
  have hc : Function.IsPeriodicPt syracuseStep p m := hcycle
  have hmod : syracuseStep^[j] m = syracuseStep^[i] m := hc.iterate_mod_apply i
  refine ⟨j,Nat.mod_lt _ hpPos,?_,hmod.trans_lt hi⟩
  by_contra hsmall
  have hjPositive : 0 < syracuseStep^[j] m := by
    cases j with
    | zero => exact hm
    | succ t =>
      rw [Function.iterate_succ_apply']
      exact Nat.ordCompl_pos 2 (by omega)
  have hreturn : syracuseStep^[p] (syracuseStep^[j] m) = syracuseStep^[j] m := by
    rw [← Function.iterate_add_apply, Nat.add_comm p j, Function.iterate_add_apply,hcycle]
  have hone := syracuse_no_cycle_below_1241513984 _ p hjPositive hpPos
    (Nat.lt_of_not_ge hsmall) hreturn
  exact hne (syracuse_periodic_reaches_one _ _ hpPos hcycle ⟨j,hone⟩)

/-- The first admissible positive period must visit a fixed finite interval. -/
theorem solution (m : ℕ) (hm : 0 < m)
    (hcycle : syracuseStep^[79335] m = m) (hne : m ≠ 1) :
    ∃ i < 79335, 1241513984 ≤ syracuseStep^[i] m ∧ syracuseStep^[i] m < 6150000000 :=
  finite_window m 79335 hm rfl hcycle hne
