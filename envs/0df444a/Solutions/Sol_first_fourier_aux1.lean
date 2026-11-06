-- Prove2me | solution 1 for first_fourier_aux1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:30:58.269875+00:00
-- url     : https://prove2.me/submissions/f093cd89-4b87-4ed8-a57f-403a7f40760b

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

open Real MeasureTheory
open scoped Topology

attribute [fun_prop] Real.continuous_fourierChar

theorem solution {ψ : ℝ → ℂ} (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  simp_rw [Circle.smul_def]
  apply AEMeasurable.enorm
  apply AEMeasurable.mul _ hψ
  exact (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop))).measurable.aemeasurable
