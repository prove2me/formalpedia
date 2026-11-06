-- Prove2me | solution 1 for decay_bounds_W21
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:32:52.05919+00:00
-- url     : https://prove2.me/submissions/49992de9-da8a-4d0e-a7a1-f67b61aabb20

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Theorems.Thm_decay_bounds_key
set_option autoImplicit true
open Real BigOperators MeasureTheory Filter Set FourierTransform SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

private lemma integral_norm_le_pi_mul {A : ℝ} {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume)
    (h : ∀ t, ‖g t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖g t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hg (Eventually.of_forall h)).norm l1 h

theorem solution (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply integral_norm_le_pi_mul f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv]
    exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply integral_norm_le_pi_mul f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv]
    exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0]
  gcongr
