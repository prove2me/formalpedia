-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
-- name    : AvramDividend.Classical.avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:28:15.682149+00:00
-- url     : https://prove2.me/theorems/924841f4-35ba-4885-9deb-1fdb8158c65c
-- title:
--   Original BV drift minus triplet drift equals minus the strict small-negative first-moment compensator
-- statement:
--   The physical BV drift coefficient of the original spectrally negative Lévy process is X.c minus the signed first moment of original negative Lévy marks in the strict open band (-1,0). Consequently X.drift-X.c equals the negative of that original smallmark moment. This identity confirms the endpoint z=-1 belongs to the large jump integral and is not compensated. Holds by the exact original drift definition on the same Ω,P,filtration, with no new noise.
-- source:
--   Exact public SpectrallyNegativeLevy.drift definition; Avram, Palmowski and Pistorius 2007, generator and Lévy–Itô truncation convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.drift - X.c =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by sorry
