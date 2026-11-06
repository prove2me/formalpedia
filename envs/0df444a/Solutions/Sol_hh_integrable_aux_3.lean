-- Prove2me | solution 3 for hh_integrable_aux
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:41.486185+00:00
-- url     : https://prove2.me/submissions/0d9c1e37-b030-4b5b-a663-03259a07132e

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

theorem solution (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by
  set F : ℝ → ℝ := fun t ↦ a * hh b (t / c) with hF
  have himg : (fun s : ℝ => c * Real.exp s) '' Set.univ = Ioi 0 := by
    ext y
    simp only [Set.image_univ, Set.mem_range, mem_Ioi]
    constructor
    · rintro ⟨s, rfl⟩; positivity
    · intro hy
      exact ⟨Real.log (y / c), by rw [Real.exp_log (by positivity)]; field_simp⟩
  have hder : ∀ s ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun s : ℝ => c * Real.exp s)
      (c * Real.exp s) Set.univ s := fun s _ =>
    ((Real.hasDerivAt_exp s).const_mul c).hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => c * Real.exp s) Set.univ := by
    intro x _ y _ h
    simpa [hc.ne'] using h
  have hpt : ∀ s : ℝ, |c * Real.exp s| • F (c * Real.exp s) = a * c * (1 + (b * s) ^ 2)⁻¹ := by
    intro s
    have : c * Real.exp s / c = Real.exp s := by field_simp
    simp only [hF, this, hh, Real.log_exp, smul_eq_mul]
    rw [abs_of_pos (by positivity)]
    have : (1 + (b * s) ^ 2) ≠ 0 := by positivity
    field_simp
  have hI : MeasureTheory.Integrable (fun s : ℝ => a * c * (1 + (b * s) ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq).comp_mul_left' (g := fun x : ℝ => (1 + x ^ 2)⁻¹)
      hb.ne'
    exact this.const_mul (a * c)
  have hint : IntegrableOn F (Ioi 0) := by
    rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj]
    simp_rw [hpt]
    exact hI.integrableOn
  refine ⟨?_, ?_⟩
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hint
  · show ∫ t in Ioi 0, F t = _
    rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj]
    simp_rw [hpt]
    rw [Measure.restrict_univ, integral_const_mul,
      Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) b, integral_univ_inv_one_add_sq]
    simp only [smul_eq_mul, abs_inv, abs_of_pos hb]
    field_simp
