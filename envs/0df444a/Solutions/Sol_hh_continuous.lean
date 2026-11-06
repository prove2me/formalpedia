-- Prove2me | solution 1 for hh_continuous
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:25:01.276955+00:00
-- url     : https://prove2.me/submissions/8879691b-87d8-4bf6-8df7-4e8950ac9c1d

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal

theorem solution (a : ℝ) : ContinuousOn (hh a) (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : ContinuousAt (fun t : ℝ => Real.log t) x := Real.continuousAt_log hx0
  have hden : ContinuousAt (fun t : ℝ => t * (1 + (a * Real.log t) ^ 2)) x := by
    fun_prop
  exact (hden.inv₀ (by
    have hsq : 0 ≤ (a * Real.log x) ^ 2 := sq_nonneg _
    have hpos : 0 < 1 + (a * Real.log x) ^ 2 := by linarith
    exact mul_ne_zero hx0 (ne_of_gt hpos))).continuousWithinAt
