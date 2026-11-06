-- Prove2me | solution 1 for gg_l1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:22.927783+00:00
-- url     : https://prove2.me/submissions/11e66901-e3db-49ec-90f6-d802b0d5db63

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

theorem solution {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  have hsq : 0 ≤ (1 / (2 * π) * log ((n : ℝ) / x)) ^ 2 := sq_nonneg _
  have hbase : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  have hfactor : (1 + (1 / (2 * π) * log ((n : ℝ) / x)) ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    linarith
  rw [gg, abs_of_nonneg (mul_nonneg hbase (inv_nonneg.mpr (by positivity)))]
  simpa using mul_le_mul_of_nonneg_left hfactor hbase
