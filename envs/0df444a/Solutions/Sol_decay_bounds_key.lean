-- Prove2me | solution 1 for decay_bounds_key
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:52:42.954088+00:00
-- url     : https://prove2.me/submissions/ce9e3151-b2f6-4abc-b2b4-a86b8e797b70

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

private theorem w21_differentiable (f : W21) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

private theorem w21_integrable (f : W21) : Integrable f :=
  f.integrable zero_le_two

private theorem w21_integrable_deriv (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

private theorem w21_integrable_deriv_deriv (f : W21) : Integrable (deriv (deriv f)) := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

@[simp] private theorem w21_fourier_neg_aux {f : ℝ → ℂ} {u : ℝ} :
    𝓕 (fun x => -f x) u = -𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] private theorem w21_fourier_add_aux {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  exact congr_fun (VectorFourier.fourierIntegral_add continuous_fourierChar continuous_inner hf hg) x

@[simp] private theorem w21_fourier_sub_aux {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using w21_fourier_add_aux hf hg.neg x

@[simp] private theorem w21_fourier_const_mul_aux {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

private theorem fourier_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have hf : Integrable f := w21_integrable f
  have hf' : Integrable (deriv f) := w21_integrable_deriv f
  have hf'' : Integrable (deriv (deriv f)) := w21_integrable_deriv_deriv f
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul
    simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := w21_differentiable f
  have l5 : Differentiable ℝ (deriv f) := f.deriv.smooth.differentiable (by simp)
  simp [hf, l1, add_mul, Real.fourier_deriv hf' l5 hf'', Real.fourier_deriv hf l4 hf']
  field_simp [pi_ne_zero]
  ring_nf
  simp

theorem solution (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast
    simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourier_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [w21_fourier_sub_aux (w21_integrable f)
    ((w21_integrable_deriv_deriv f).const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, w21_fourier_const_mul_aux, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm
