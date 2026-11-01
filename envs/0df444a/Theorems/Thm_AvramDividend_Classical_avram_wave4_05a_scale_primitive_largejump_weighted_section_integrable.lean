-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_scale_primitive_largejump_weighted_section_integrable
-- name    : AvramDividend.Classical.avram_wave4_05a_scale_primitive_largejump_weighted_section_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:50:48.115592+00:00
-- url     : https://prove2.me/theorems/6e08ca30-3433-432c-8db7-e400b172a368
-- title:
--   Uniform weighted integrability of original large-jump generator sections for the integrated q-scale function
-- statement:
--   For a genuine source q-scale W with positive Laplace parameter θ and q<ψ(θ), its causal oriented interval primitive U(x)=∫0^x W is nonnegative, nondecreasing, and exponentially integrable with mass [(ψ(θ)-q)θ]⁻¹. For each negative jump of magnitude at least one, the actual original Lévy generatorIntegrand U x (-r) contains no compensation term, equals U(x-r)-U(x), and its positive-state exponentially weighted absolute-value section is genuinely integrable and uniformly bounded by the primitive Laplace mass. No Gaussian assumption, finite activity at zero, assumed generator integrability or q-harmonicity is used.
-- source:
--   Genuine missing large-jump primitive L1 input in source non-Gaussian pure C2 harmonicity route to P2-owned e8fbc763-da83-4909-b759-27feee641e80; original source generator 933ced80 and scale definition e6610c46; Proved primitive zero support 6dcc8ffe, positive Laplace interval primitive 9f40ea02, source uncompensated kernel 4809dc4e. It pairs with finite ν([-∞,-1]) for Fubini; proposed child has no published decomposition edge and does not assert parent's harmonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05a_scale_primitive_largejump_weighted_section_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 1 ≤ r) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
       |SpectrallyNegativeLevy.generatorIntegrand
         (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      (X.ψ θ - q)⁻¹ / θ := by sorry
