-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded
-- name    : AvramDividend.Classical.avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T12:32:27.735962+00:00
-- url     : https://prove2.me/theorems/a74e690b-1c59-48ac-b3f6-2266f40e75cc
-- title:
--   Zero jumps and unbounded variation imply nonzero Gaussian coefficient
-- statement:
--   For an original spectrally negative Lévy process with zero jump measure, failure of bounded variation forces its Gaussian coefficient to be nonzero.
-- source:
--   Direct logical consequence of the original Avram bounded-variation definition, prerequisite for Gaussian stopped reward 642de490 and d65c7756.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) : X.σ ≠ 0 := by sorry
