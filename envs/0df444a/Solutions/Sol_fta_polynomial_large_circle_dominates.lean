-- Prove2me | solution 1 for fta_polynomial_large_circle_dominates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-03T21:40:32.144809+00:00
-- url     : https://prove2.me/submissions/ee64de02-f068-4437-a571-f9c2dd3a7786

import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Definitions.Def_fta_winding_infra

noncomputable section
open Complex Polynomial
open scoped Real

theorem solution (f : Polynomial ℂ) (hf : 0 < f.degree) :
    ∃ R : ℝ, 0 < R ∧ FtaLeadingDominatesOnBoundary f R := by
  have hf0 : f ≠ 0 := fun h => by simp [h] at hf
  have hn1 : 1 ≤ f.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr hf
  set n := f.natDegree with hndef
  set lc := f.leadingCoeff with hlcdef
  have hlc0 : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hlcpos : 0 < ‖lc‖ := norm_pos_iff.mpr hlc0
  set g := f.eraseLead with hgdef
  have hglt : g.natDegree < n := by
    by_cases hg0 : g = 0
    · simp [hg0]; omega
    · exact Polynomial.natDegree_lt_natDegree hg0 (Polynomial.degree_eraseLead_lt hf0)
  set C := ∑ i ∈ Finset.range n, ‖g.coeff i‖ with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  set R := max 1 (C / ‖lc‖ + 1) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRbig : C < ‖lc‖ * R := by
    have h2 : C / ‖lc‖ + 1 ≤ R := le_max_right _ _
    have : C / ‖lc‖ < R := by linarith
    calc C = ‖lc‖ * (C / ‖lc‖) := by field_simp
      _ < ‖lc‖ * R := by exact mul_lt_mul_of_pos_left this hlcpos
  have core : ∀ z : ℂ, ‖z‖ = R → ‖g.eval z‖ < ‖lc‖ * R ^ n := by
    intro z hz
    have hzge1 : 1 ≤ ‖z‖ := by rw [hz]; exact hR1
    have hbound : ‖g.eval z‖ ≤ C * ‖z‖ ^ (n - 1) := by
      rw [Polynomial.eval_eq_sum_range' hglt z]
      refine le_trans (norm_sum_le _ _) ?_
      rw [hCdef, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply pow_le_pow_right₀ hzge1
      have : i < n := Finset.mem_range.mp hi
      omega
    have hstep : C * ‖z‖ ^ (n - 1) < ‖lc‖ * R ^ n := by
      have hRpow : (0 : ℝ) < R ^ (n - 1) := by positivity
      have hsplit : R ^ n = R * R ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ']
      rw [hz, hsplit]
      calc C * R ^ (n - 1) < (‖lc‖ * R) * R ^ (n - 1) := by
              exact mul_lt_mul_of_pos_right hRbig hRpow
        _ = ‖lc‖ * (R * R ^ (n - 1)) := by ring
    exact lt_of_le_of_lt hbound hstep
  have main : ∀ θ : FtaCircle,
      f.eval (FtaBoundaryPoint R θ) ≠ 0 ∧
      FtaStraightLineNonzero (f.eval (FtaBoundaryPoint R θ)) (FtaLeadingTermBoundary f R θ) := by
    intro θ
    set z : ℂ := FtaBoundaryPoint R θ with hzdef
    have hznorm : ‖z‖ = R := by
      rw [hzdef, FtaBoundaryPoint, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
        Real.norm_of_nonneg hRpos.le]
    set a : ℂ := f.eval z with hadef
    set L : ℂ := FtaLeadingTermBoundary f R θ with hLdef
    have hLeq : L = lc * z ^ n := rfl
    have hLnorm : ‖L‖ = ‖lc‖ * R ^ n := by rw [hLeq, norm_mul, norm_pow, hznorm]
    have haL : a - L = g.eval z := by
      have h := congrArg (Polynomial.eval z) (Polynomial.self_sub_C_mul_X_pow f)
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at h
      rw [hadef, hLeq]; exact h
    have hest : ‖a - L‖ < ‖L‖ := by rw [haL, hLnorm]; exact core z hznorm
    have hLpos : 0 < ‖L‖ := by rw [hLnorm]; positivity
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, zero_sub, norm_neg] at hest
      exact lt_irrefl _ hest
    · intro t hcontra
      set τ : ℝ := (t : ℝ) with hτ
      have hτ0 : 0 ≤ τ := t.2.1
      have hτ1 : τ ≤ 1 := t.2.2
      have hid : (1 - (τ : ℂ)) * a + (τ : ℂ) * L
          = L + (1 - (τ : ℂ)) * (a - L) := by ring
      rw [hid] at hcontra
      have hLval : L = -((1 - (τ : ℂ)) * (a - L)) := by linear_combination hcontra
      have hnorm : ‖L‖ = (1 - τ) * ‖a - L‖ := by
        conv_lhs => rw [hLval]
        rw [norm_neg, norm_mul]
        congr 1
        rw [show (1 : ℂ) - (τ : ℂ) = ((1 - τ : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have : (1 - τ) * ‖a - L‖ ≤ ‖a - L‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (by linarith)
      linarith [hnorm, hest]
  exact ⟨R, hRpos, fun θ => (main θ).1, fun θ => (main θ).2⟩
