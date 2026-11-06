-- Prove2me | solution 3 for summable_fourier_aux
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:55.415612+00:00
-- url     : https://prove2.me/submissions/330ea21c-1aa1-4946-b806-b36058e4e721

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
variable (f x)

theorem PNAux.decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have hsm : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) (f : ℝ → ℂ) := by exact_mod_cast f.smooth
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv k (f : ℝ → ℂ)) :=
    fun k hk => f.integrable (by exact_mod_cast hk)
  have h0 : Integrable (f : ℝ → ℂ) := by simpa using f.integrable (k := 0) (by norm_num)
  have h2 := Real.fourier_iteratedDeriv (n := 2) hsm hint (by norm_num)
  have hd2' : ∀ φ : ℝ → ℂ, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hd2 := hd2' (f : ℝ → ℂ)
  have hb0 : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ∫ v, ‖(f : ℝ → ℂ) v‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hb2 : ‖𝓕 (iteratedDeriv 2 (f : ℝ → ℂ)) u‖ ≤ ∫ v, ‖deriv (deriv (f : ℝ → ℂ)) v‖ := by
    rw [← hd2]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [h2] at hb2
  simp only [norm_smul, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I,
    Real.norm_eq_abs, Complex.norm_ofNat, abs_of_pos Real.pi_pos, mul_one] at hb2
  have hπ : 0 < π := Real.pi_pos
  have h3 : u ^ 2 * ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv (f : ℝ → ℂ)) v‖ := by
    rw [← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    have : (2 * π * |u|) ^ 2 = 4 * π ^ 2 * u ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [this] at hb2
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  show _ ≤ (∫ v, ‖(f : ℝ → ℂ) v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖deriv (deriv (f : ℝ → ℂ)) v‖
  nlinarith

theorem solution (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  rw [norm_mul, norm_div, Complex.norm_natCast]
  have h := PNAux.decay_bounds_key ψ (1 / (2 * π) * Real.log (i / x))
  have h0 : 0 ≤ ‖f i‖ / i := by positivity
  calc ‖f i‖ / i * ‖𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖
      ≤ ‖f i‖ / i * (‖ψ‖ * (1 + (1 / (2 * π) * Real.log (i / x)) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h h0
    _ = W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
        show _ = ‖ψ‖ * _
        ring
