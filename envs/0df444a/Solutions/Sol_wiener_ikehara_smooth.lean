-- Prove2me | solution 1 for wiener_ikehara_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:47.057956+00:00
-- url     : https://prove2.me/submissions/61d8fa04-3428-4edf-838d-8c7574900333

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
import Theorems.Thm_continuous_FourierIntegral
import Theorems.Thm_cumsum_zero
import Theorems.Thm_nabla_cumsum
import Theorems.Thm_nabla_mul
import Theorems.Thm_nnabla_mul
import Theorems.Thm_limiting_cor_schwartz
import Theorems.Thm_fourier_surjection_on_schwartz
import Theorems.Thm_toSchwartz_apply
import Theorems.Thm_comp_exp_support0
import Theorems.Thm_comp_exp_support
import Theorems.Thm_wiener_ikehara_smooth_aux
import Theorems.Thm_wiener_ikehara_smooth_sub
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


attribute [local continuity] continuous_multiplicative_ofAdd
attribute [local continuity] continuous_FourierIntegral
attribute [local fun_prop] continuous_FourierIntegral
attribute [local simp] cumsum_zero
attribute [local simp] nabla_cumsum
attribute [local simp] nabla_mul
attribute [local simp] nnabla_mul
attribute [local simp] toSchwartz_apply

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
theorem _root_.solution (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have hπ : 2 * π ≠ 0 := by simp [pi_ne_zero]
    have hh : HasCompactSupport (fun x : ℝ => Ψ (rexp (2 * π * x))) := by
      simpa only [Function.comp_def, smul_eq_mul] using
        (comp_exp_support hsupp hplus).comp_smul hπ
    change HasCompactSupport
      ((fun x : ℝ => (rexp (2 * π * x) : ℂ)) * fun x : ℝ => Ψ (rexp (2 * π * x)))
    exact hh.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)
  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    rw [hg]
    change (y : ℂ) * Ψ y = h (1 / (2 * π) * Real.log y)
    have harg : 2 * π * (1 / (2 * π) * Real.log y) = Real.log y := by
      rw [← mul_assoc, mul_one_div_cancel (mul_ne_zero (by norm_num) pi_ne_zero), one_mul]
    dsimp only [h]
    rw [harg, Real.exp_log hy]
  have key := limiting_cor_schwartz g hf hcheby hG hG'
  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp
  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    rw [hg]
    change (∫ u in Ici (-Real.log x), h (u / (2 * π))) = ∫ y in Ioi x⁻¹, Ψ y
    dsimp only [h]
    have hscale : (2 : ℝ) * π ≠ 0 := mul_ne_zero (by norm_num) pi_ne_zero
    have harg (u : ℝ) : 2 * π * (u / (2 * π)) = u := mul_div_cancel₀ u hscale
    simp_rw [harg]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    simpa only [one_div] using wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx
  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus
  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4
