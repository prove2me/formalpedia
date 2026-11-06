-- Prove2me | solution 3 for isLittleO_mul_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:53.857457+00:00
-- url     : https://prove2.me/submissions/fce8f1e7-8b4a-40c5-a7fb-50dcc4dc65fc

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

theorem PNAux.isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  rw [Asymptotics.isLittleO_const_left]
  right
  exact tendsto_norm_atTop_atTop.comp hf

theorem solution (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  have h1 : (fun x : ℝ => a * x) =o[atTop] (fun x : ℝ => x ^ 2) := by
    have := (Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show 1 < 2 by norm_num))
    simpa [mul_comm] using this.const_mul_left a
  have h2 : (fun _ : ℝ => b) =o[atTop] (fun x : ℝ => x ^ 2) :=
    PNAux.isLittleO_const_of_tendsto_atTop b (tendsto_pow_atTop (by norm_num))
  exact h1.add h2
