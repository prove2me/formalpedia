-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_global_monotone
-- name    : AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_global_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:55:50.20867+00:00
-- url     : https://prove2.me/theorems/226a1286-7943-4fde-badf-601156bd423d
-- title:
--   Original scale primitive is globally monotone including its zero-extension boundary
-- statement:
--   The actual integrated q-scale function U(z)=∫₀ᶻW(t)dt is nondecreasing across the entire real line for any genuine source IsScaleFunction, including its extension to negative reserves, without positivity of q, unbounded variation or Gaussian smoothness. Because the original W vanishes below zero and is nonnegative on nonnegative reserves, U vanishes on nonpositive states and increases on nonnegative states. This standalone source fact supplies globally measurable U and large-jump monotone dominance for the non-Gaussian primitive generator product Fubini and its signed variant.
-- source:
--   Avram Palmowski Pistorius (2007), Section 3 scale function positivity; exact P2 zero-support lemma 6dcc8ffe and original scale interval integrability fc543d73; source-faithful monotone primitive argument independently checked in accepted Chat05a large-jump kernel proof 6e08ca30.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_source_scale_primitive_global_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Monotone (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) := by sorry
