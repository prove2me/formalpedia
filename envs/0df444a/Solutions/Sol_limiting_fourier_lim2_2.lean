-- Prove2me | solution 2 for limiting_fourier_lim2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:49:23.609665+00:00
-- url     : https://prove2.me/submissions/4c5429ff-5582-4157-b038-69545857145a

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
import Theorems.Thm_continuous_multiplicative_ofAdd
import Theorems.Thm_decay_bounds_cor
import Theorems.Thm_continuous_FourierIntegral
import Theorems.Thm_cumsum_zero
import Theorems.Thm_nabla_cumsum
import Theorems.Thm_nabla_mul
import Theorems.Thm_nnabla_mul
import Theorems.Thm_limiting_fourier_lim2_aux
import Theorems.Thm_F_add
import Theorems.Thm_F_mul
import Theorems.Thm_F_neg
import Theorems.Thm_F_sub
import Theorems.Thm_OAI_QRH_b83dbbd_deriv_ofReal
import Theorems.Thm_W21_norm_nonneg
attribute [local simp] F_add
attribute [local simp] F_mul
attribute [local simp] F_neg
attribute [local simp] F_sub
attribute [local simp] OAI.QRH_b83dbbd.deriv_ofReal


attribute [local continuity] continuous_multiplicative_ofAdd
attribute [local continuity] continuous_FourierIntegral
attribute [local fun_prop] continuous_FourierIntegral
attribute [local simp] cumsum_zero
attribute [local simp] nabla_cumsum
attribute [local simp] nabla_mul
attribute [local simp] nnabla_mul

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
attribute [local gcongr] _root_.norm_lt_norm_of_nonneg
theorem _root_.solution (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' hσ
        have h1 := hσ.1
        have h2 := hσ.2
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity
