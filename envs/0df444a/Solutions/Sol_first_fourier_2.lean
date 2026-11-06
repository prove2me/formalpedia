-- Prove2me | solution 2 for first_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:47:55.557201+00:00
-- url     : https://prove2.me/submissions/f98d0ab3-1d8a-4d77-a2f1-ef1986766068

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
import Theorems.Thm_norm_term_eq_nterm_re
import Theorems.Thm_hf_coe1
import Theorems.Thm_first_fourier_aux1
import Theorems.Thm_first_fourier_aux2
import Theorems.Thm_F_add
import Theorems.Thm_F_mul
import Theorems.Thm_F_neg
import Theorems.Thm_F_sub
import Theorems.Thm_OAI_QRH_b83dbbd_deriv_ofReal
import Theorems.Thm_W21_hf
attribute [local simp] F_add
attribute [local simp] F_mul
attribute [local simp] F_neg
attribute [local simp] F_sub
attribute [local simp] OAI.QRH_b83dbbd.deriv_ofReal



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
theorem _root_.solution (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by
  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun n ↦ AEMeasurable.aestronglyMeasurable ?_
        change AEMeasurable (fun v : ℝ => term f σ' n *
          (((fourierChar (-(v * (1 / (2 * π) * Real.log (n / x))))) : ℂ) * ψ v)) volume
        exact aemeasurable_const.mul ((by fun_prop :
          AEMeasurable (fun v : ℝ => ((fourierChar
            (-(v * (1 / (2 * π) * Real.log (n / x))))) : ℂ)) volume).mul hsupp.aemeasurable)
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp only [enorm_eq_nnnorm, nnnorm, Circle.norm_smul]
            convert (ENNReal.tsum_mul_right (f := fun i : ℕ => ‖term f σ' i‖ₑ)
              (a := ∫⁻ (a : ℝ), ‖ψ a‖ₑ)) using 1 <;> rfl
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp
