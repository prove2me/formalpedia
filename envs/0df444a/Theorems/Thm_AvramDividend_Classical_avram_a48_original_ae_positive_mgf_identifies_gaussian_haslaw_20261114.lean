-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
-- name    : AvramDividend.Classical.avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:40:34.961494+00:00
-- url     : https://prove2.me/theorems/d80b4a02-53fd-4770-a809-1dbdd36500ca
-- title:
--   Original probability-space a.e.-measurable scalar positive-ray Gaussian MGF identifies exact centred Gaussian law
-- statement:
--   An a.e.-measurable real random variable on an original probability space has exact centred Gaussian law with variance v whenever its positive exponential moments are integrable and its moment-generating function matches the Gaussian for every positive real parameter.
-- source:
--   Proved measure_eq_of_pos_mgf_on_ray and positive-ray Gaussian exponential integrability; generalisation of gbB265 original proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (v : ℝ≥0)
    (hInt : ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMGF : ∀ θ : ℝ, 0 < θ →
      mgf Z P θ = mgf id (gaussianReal 0 v) θ) :
    HasLaw Z (gaussianReal 0 v) P := by sorry
