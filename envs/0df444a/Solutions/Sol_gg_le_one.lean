-- Prove2me | solution 1 for gg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:23:46.184858+00:00
-- url     : https://prove2.me/submissions/e92c622d-3006-4bba-8abd-8870684cee46

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

theorem gg_le_one_solution_aux (i : ℕ) : gg x i ≤ 1 := by
  cases i with
  | zero => simp [gg]
  | succ i =>
    unfold gg
    have hi_pos : (0 : ℝ) < ↑(i + 1) := by positivity
    have hi_one : (1 : ℝ) ≤ ↑(i + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)
    have hfirst : 1 / (↑(i + 1) : ℝ) ≤ 1 := (div_le_iff₀ hi_pos).2 (by simpa using hi_one)
    have hden_pos : (0 : ℝ) <
        1 + (1 / (2 * π) * log (↑(i + 1) / x)) ^ 2 := by positivity
    have hden_one : (1 : ℝ) ≤ 1 + (1 / (2 * π) * log (↑(i + 1) / x)) ^ 2 := by
      nlinarith [sq_nonneg (1 / (2 * π) * log (↑(i + 1) / x))]
    have hsecond : (1 + (1 / (2 * π) * log (↑(i + 1) / x)) ^ 2)⁻¹ ≤ 1 :=
      (inv_le_one₀ hden_pos).2 hden_one
    have hsecond_nonneg : 0 ≤ (1 + (1 / (2 * π) * log (↑(i + 1) / x)) ^ 2)⁻¹ :=
      (inv_pos.mpr hden_pos).le
    calc
      1 / (↑(i + 1) : ℝ) * (1 + (1 / (2 * π) * log (↑(i + 1) / x)) ^ 2)⁻¹
          ≤ 1 * 1 := mul_le_mul hfirst hsecond hsecond_nonneg (by norm_num)
      _ = 1 := one_mul 1

theorem solution (i : ℕ) : gg x i ≤ 1 := by
  exact gg_le_one_solution_aux i
