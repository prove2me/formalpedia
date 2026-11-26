-- Prove2me | solution 1 for section5_l2_add_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:49.258289+00:00
-- url     : https://prove2.me/submissions/8a4d3de7-21e4-4f13-9f3b-bd0b476316d1

import Mathlib
import Theorems.Thm_section5_l2_norm_sq
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/



theorem section5_l2_energy_triangle {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, ‖f x+g x‖^2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖^2 ∂μ)+Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have ha : (hf.add hg).toLp (f+g) = hf.toLp f+hg.toLp g := by
    apply Lp.ext
    filter_upwards [(hf.add hg).coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,
      Lp.coeFn_add (hf.toLp f) (hg.toLp g)] with x hsum hfx hgx hadd
    simp only [hsum,hadd,Pi.add_apply,hfx,hgx]
  rw [← section5_l2_norm_sq f hf,← section5_l2_norm_sq g hg]
  change Real.sqrt (∫ x, ‖(f+g) x‖^2 ∂μ) ≤ _
  rw [← section5_l2_norm_sq (f+g) (hf.add hg),ha]
  simpa only [Real.sqrt_sq (norm_nonneg _)] using norm_add_le (hf.toLp f) (hg.toLp g)













































end
set_option autoImplicit false
open MeasureTheory
theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (A B S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hfa : (∫ x, ‖f x‖^2 ∂μ) ≤ A^2*S)
    (hgb : (∫ x, ‖g x‖^2 ∂μ) ≤ B^2*S) :
    (∫ x, ‖f x+g x‖^2 ∂μ) ≤ (A+B)^2*S := by
  have hfs : Real.sqrt (∫ x, ‖f x‖^2 ∂μ) ≤ A*Real.sqrt S := by
    convert Real.sqrt_le_sqrt hfa using 1
    rw [Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq hA]
  have hgs : Real.sqrt (∫ x, ‖g x‖^2 ∂μ) ≤ B*Real.sqrt S := by
    convert Real.sqrt_le_sqrt hgb using 1
    rw [Real.sqrt_mul (sq_nonneg B),Real.sqrt_sq hB]
  have hh := (section5_l2_energy_triangle f g hf hg).trans (add_le_add hfs hgs)
  have hh' : Real.sqrt (∫ x, ‖f x+g x‖^2 ∂μ) ≤ (A+B)*Real.sqrt S := by
    simpa only [add_mul] using hh
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh' 2
  rw [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),mul_pow,Real.sq_sqrt hS] at hsq
  exact hsq
