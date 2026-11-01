-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:29:27.308797+00:00
-- url     : https://prove2.me/theorems/f587f475-1405-44cf-aae2-2b6ebd96d4d4
-- title:
--   Exact source generator crossing jump kernel has weighted quadratic x-mass
-- statement:
--   For the original source compensated negative small-jump generator integrand acting on U=∫_0^x W, its exponentially weighted x-section on the boundary-crossing strip 0<x<r<1 is integrable and bounded above by W(1)r². It uses the exact source kernel crossing identity 570d4d46 and the previously established weighted primitive strip estimate 8516e7bf. This is the missing boundary half of the actual source quadratic x-section jump-product argument, pairing directly with the Proved interior source weighted bound c0fb07f0.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4; canonical source kernel 570d4d46 and weighted crossing 8516e7bf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_crossing_weighted_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|)
      (Ioo (0 : ℝ) r) volume ∧
    (∫ x in Ioo (0 : ℝ) r,
      Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤
      W 1 * r^2 := by sorry
