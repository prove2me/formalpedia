-- Prove2me | solution 1 for nnabla_mul_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:34:20.013753+00:00
-- url     : https://prove2.me/submissions/eae2341f-d2d0-4275-b02a-058f0ab726b7

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

theorem solution (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by
  have hcore (a x u d : ℝ) (hx : 1 ≤ x) (hu : 0 ≤ u) (hd : 0 ≤ d)
      (hxd : x * d ≤ 1) :
      |(x + 1) * (a + (u + d) ^ 2) - x * (a + u ^ 2)| ≤
        |a| + (u + d) ^ 2 + 2 * u + d := by
    have hx0 : 0 ≤ x := by linarith
    have hdiff : 0 ≤ (u + d) ^ 2 - u ^ 2 := by
      nlinarith [mul_nonneg hu hd, sq_nonneg d]
    have hr : 0 ≤ (u + d) ^ 2 + x * ((u + d) ^ 2 - u ^ 2) :=
      add_nonneg (sq_nonneg _) (mul_nonneg hx0 hdiff)
    have hprod : x * d * (2 * u + d) ≤ 2 * u + d := by
      have hnon : 0 ≤ 2 * u + d := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hxd) hnon]
    calc
      |(x + 1) * (a + (u + d) ^ 2) - x * (a + u ^ 2)| =
          |a + ((u + d) ^ 2 + x * ((u + d) ^ 2 - u ^ 2))| := by
            congr 1
            ring
      _ ≤ |a| + |(u + d) ^ 2 + x * ((u + d) ^ 2 - u ^ 2)| := abs_add_le _ _
      _ = |a| + ((u + d) ^ 2 + x * ((u + d) ^ 2 - u ^ 2)) := by
            rw [abs_of_nonneg hr]
      _ ≤ |a| + (u + d) ^ 2 + 2 * u + d := by
            nlinarith
  refine isBigO_iff.mpr ⟨|a| + 14, ?_⟩
  filter_upwards [eventually_ge_atTop b, eventually_ge_atTop b⁻¹,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.exp 1)] with x hxb hxbi hx1 hxe
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hu0 : 0 ≤ Real.log (x / b) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hb).mpr (by simpa using hxb)
  have hbi : -Real.log b ≤ Real.log x := by
    calc
      -Real.log b = Real.log b⁻¹ := (Real.log_inv b).symm
      _ ≤ Real.log x := Real.log_le_log (inv_pos.mpr hb) hxbi
  have hu2 : Real.log (x / b) ≤ 2 * Real.log x := by
    rw [Real.log_div hx0.ne' hb.ne']
    linarith
  have hL : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hxe
  have hd0 : 0 ≤ Real.log ((x + 1) / x) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hx0).mpr (by linarith)
  have hxd : x * Real.log ((x + 1) / x) ≤ 1 := by
    have hdle : Real.log ((x + 1) / x) ≤ 1 / x := by
      calc
        Real.log ((x + 1) / x) ≤ (x + 1) / x - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        _ = 1 / x := by field_simp; ring
    calc
      x * Real.log ((x + 1) / x) ≤ x * (1 / x) :=
        mul_le_mul_of_nonneg_left hdle hx0.le
      _ = 1 := by field_simp
  have hd1 : Real.log ((x + 1) / x) ≤ 1 := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hx1)]
  have hlog : Real.log ((x + 1) / b) =
      Real.log (x / b) + Real.log ((x + 1) / x) := by
    rw [Real.log_div (by positivity) hb.ne', Real.log_div hx0.ne' hb.ne',
      Real.log_div (by positivity) hx0.ne']
    ring
  simp only [nabla]
  rw [hlog, Real.norm_eq_abs, norm_of_nonneg (sq_nonneg (Real.log x))]
  have hu_sq : (Real.log (x / b)) ^ 2 ≤ (2 * Real.log x) ^ 2 := by
    nlinarith [mul_le_mul hu2 hu2 hu0 (by linarith : 0 ≤ 2 * Real.log x)]
  have hud : Real.log (x / b) * Real.log ((x + 1) / x) ≤ 2 * Real.log x := by
    calc
      Real.log (x / b) * Real.log ((x + 1) / x) ≤ (2 * Real.log x) * 1 :=
        mul_le_mul hu2 hd1 hd0 (by linarith)
      _ = 2 * Real.log x := by ring
  have hd_sq : (Real.log ((x + 1) / x)) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  have hL_sq : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith
  calc
    |(x + 1) * (a + (Real.log (x / b) + Real.log ((x + 1) / x)) ^ 2) -
        x * (a + Real.log (x / b) ^ 2)| ≤
      |a| + (Real.log (x / b) + Real.log ((x + 1) / x)) ^ 2 +
        2 * Real.log (x / b) + Real.log ((x + 1) / x) :=
      hcore a x _ _ hx1 hu0 hd0 hxd
    _ ≤ (|a| + 14) * (Real.log x) ^ 2 := by
      have ha : 0 ≤ |a| := abs_nonneg a
      have hL0 : 0 ≤ Real.log x := by linarith
      nlinarith [sq_nonneg (|a|), sq_nonneg (Real.log x), mul_nonneg ha (sq_nonneg (Real.log x))]
