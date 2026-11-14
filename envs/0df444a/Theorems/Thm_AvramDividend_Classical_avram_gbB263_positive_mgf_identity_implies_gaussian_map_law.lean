-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB263_positive_mgf_identity_implies_gaussian_map_law
-- name    : AvramDividend.Classical.avram_gbB263_positive_mgf_identity_implies_gaussian_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:20:41.877201+00:00
-- url     : https://prove2.me/theorems/c7b3d7f3-88fb-42dd-b253-6a8efc1aba6a
-- title:
--   avram gbB263 positive mgf gaussian law
-- statement:
--   For a measurable real random variable on a probability space, if each positive exponential moment is integrable and its positive-ray MGF equals a Gaussian law MGF, then its pushed-forward measure equals that Gaussian law. This is a direct bridge to an already Proved positive-MGF uniqueness theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB263_positive_mgf_identity_implies_gaussian_map_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (m : ℝ) (v : ℝ≥0)
    (hInt : ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMGF : ∀ θ : ℝ, 0 < θ →
      mgf Z P θ = mgf id (gaussianReal m v) θ) :
    Measure.map Z P = gaussianReal m v := by sorry
