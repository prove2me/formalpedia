-- Prove2me | solution 1 for second_fourier_integrable_aux2
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:09.688192+00:00
-- url     : https://prove2.me/submissions/2f3fe33a-39ef-4810-90bc-c16ab3586594

import Mathlib.NumberTheory.LSeries.PrimesInAP

set_option autoImplicit true

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

theorem solution (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  apply integrableOn_exp_mul_complex_Ioi
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul]
  linarith
