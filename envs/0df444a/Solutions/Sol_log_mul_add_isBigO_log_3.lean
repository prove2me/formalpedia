-- Prove2me | solution 3 for log_mul_add_isBigO_log
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:47.239055+00:00
-- url     : https://prove2.me/submissions/55473feb-1a14-4450-9389-8b1af02fa299

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

theorem solution {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  have h1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have h2 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    have : Tendsto (fun x : ℝ => x ^ 2 - a * x - b) atTop atTop := by
      have : (fun x : ℝ => x ^ 2 - a * x - b) = fun x => x * (x - a) - b := by
        ext x; ring
      rw [this]
      refine tendsto_atTop_add_const_right _ _ ?_
      exact tendsto_id.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _ tendsto_id)
    filter_upwards [this.eventually_ge_atTop 0] with x hx
    linarith
  have h3 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := by
    have : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop ha)
    exact this.eventually_ge_atTop 1
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hx0 : 0 < x := by linarith
  have l1 : 0 ≤ Real.log (a * x + b) := Real.log_nonneg hx3
  have l2 : Real.log (a * x + b) ≤ Real.log (x ^ 2) :=
    Real.log_le_log (by linarith) hx2
  rw [Real.log_pow] at l2
  have l3 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg l1, abs_of_nonneg l3]
  push_cast at l2
  linarith
