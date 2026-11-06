-- Prove2me | solution 1 for quadratic_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:23.527331+00:00
-- url     : https://prove2.me/submissions/a58693db-0991-4b0c-8bd9-e16363854bba

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

theorem solution (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have hdisc : b ^ 2 - 4 * a * c < 0 := by
    simpa [discrim] using hΔ
  have ha4 : 0 < 4 * a := by linarith
  have key : 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
    nlinarith [sq_nonneg (2 * a * x + b)]
  exact (mul_pos_iff_of_pos_left ha4).mp key
