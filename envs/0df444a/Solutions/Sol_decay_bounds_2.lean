-- Prove2me | solution 2 for decay_bounds
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:15:25.365844+00:00
-- url     : https://prove2.me/submissions/3986e68e-9e0d-4d72-a736-3a630df7e147

import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators FourierTransform
open scoped ContDiff

variable {A u : ℝ}

private theorem w1_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

private theorem w21_integrable (f : W21) : Integrable f :=
  f.integrable zero_le_two

private theorem w21_integrable_deriv (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

private theorem w21_integrable_deriv_deriv (f : W21) : Integrable (deriv (deriv f)) := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

@[simp] private theorem decay_fourier_add' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have hcont : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  exact congr_fun (fourierIntegral_add continuous_fourierChar hcont hf hg) x

@[simp] private theorem decay_fourier_neg' {f : ℝ → ℂ} {u : ℝ} :
    𝓕 (fun x => -f x) u = -𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] private theorem decay_fourier_sub' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using decay_fourier_add' hf hg.neg x

@[simp] private theorem decay_fourier_const_mul' {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

@[simp] private theorem decay_fourier_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul
    simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := w1_differentiable f
  have l5 : Differentiable ℝ (deriv f) := w1_differentiable f.deriv
  simp [w21_integrable, w21_integrable_deriv_deriv, l1, add_mul,
    Real.fourier_deriv (w21_integrable_deriv f) l5 (w21_integrable_deriv_deriv f),
    Real.fourier_deriv (w21_integrable f) l4 (w21_integrable_deriv f)]
  field_simp [pi_ne_zero]
  ring_nf
  simp

private theorem one_add_sq_pos' (u : ℝ) : 0 < 1 + u ^ 2 :=
  zero_lt_one.trans_le (by simpa using sq_nonneg u)

private theorem decay_key (f : W21) (u : ℝ) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos' _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast
    simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := decay_fourier_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [decay_fourier_sub' (w21_integrable f)
    ((w21_integrable_deriv_deriv f).const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, decay_fourier_const_mul', norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

private theorem decay_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

private theorem decay_w21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u : ℝ) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_aux f.smooth.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv]
    exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_aux f.deriv.deriv.smooth.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv]
    exact hA'
  apply decay_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0]
  gcongr

theorem solution (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_w21 ψ hA hA' u
