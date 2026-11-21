-- Prove2me | solution 1 for moebius_summatory_rpow_bound_below_record
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T03:59:35.292887+00:00
-- url     : https://prove2.me/submissions/f410cd67-ff82-4c19-b5e4-41faaed544c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
import Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

/-!
Finite rational zero obstruction adapted from marozols's Apache-2.0 Prove2Me
submission e87e9854-dba7-4bb6-9fe7-e23f23a0a723. The analytic Littlewood
implication is imported as an already proved conditional theorem.
-/
set_option autoImplicit false
open Finset ArithmeticFunction Filter Topology

-- Finite rational zero obstruction, following the campaign solution of 12360d46.
private theorem right_zero_free (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < 2*s.re-1 := by linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (‖s‖^2 / (2*s.re-1))
  obtain ⟨c,H,hC⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  let M : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
  change M < 1/(J+1 : ℚ) at hC
  have hc : (M:ℝ) < 1/(J+1:ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr hC
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using ht
  have hh := NymanBeurling.finite_remainder_zero_obstruction s hs hs_one hz c H
  change 2*s.re-1 ≤ (M:ℝ)*‖s‖^2 at hh
  apply (not_lt_of_ge hh)
  calc
    _ ≤ (1/(J+1:ℝ))*‖s‖^2 := mul_le_mul_of_nonneg_right hc.le (sq_nonneg _)
    _ < 2*s.re-1 := by
      rw [one_div,inv_mul_eq_div,div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hpos).mp hJ
      nlinarith

private theorem rh_of_remainder_certificates : RiemannHypothesis := by
  apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
  intro s hz hpos hlt
  have hne : s ≠ 1 := by rintro rfl; norm_num at hlt
  apply le_antisymm
  · exact le_of_not_gt (fun h => right_zero_free s h hne hz)
  · by_contra! hleft
    have hzero : riemannZeta (1-s) = 0 := by
      rw [riemannZeta_one_sub _ hne,hz,mul_zero]
      intro n he
      rw [he] at hpos
      simp at hpos
      exact (Nat.cast_nonneg (α:=ℝ) n).not_gt hpos
    apply right_zero_free (1-s) (by simp; linarith) _ hzero
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith


theorem solution :
    ∀ ε : ℝ, 0 < ε → ε ≤ 0.3749570698 →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
  intro ε hε _hcap
  exact moebius_summatory_rpow_bound_of_riemannHypothesis rh_of_remainder_certificates ε hε
