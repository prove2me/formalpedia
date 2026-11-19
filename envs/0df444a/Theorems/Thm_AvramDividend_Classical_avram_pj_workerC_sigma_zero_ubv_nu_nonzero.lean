-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_sigma_zero_ubv_nu_nonzero
-- name    : AvramDividend.Classical.avram_pj_workerC_sigma_zero_ubv_nu_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:29:22.7302+00:00
-- url     : https://prove2.me/theorems/1de1db4c-c56d-4eb0-9e18-8a7df15753ef
-- title:
--   Original unbounded-variation purejump Lévy source necessarily has nonzero jump measure
-- statement:
--   For the same original SpectrallyNegativeLevy X, if X has unbounded variation and its Gaussian coefficient sigma is zero, then its Lévy measure ν is nonzero, directly by contradiction with the already Proved zero ν -> sigma≠0 theorem.
-- source:
--   Previously Proved avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded a74e690b; direct logical contrapositive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_sigma_zero_ubv_nu_nonzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    X.ν ≠ 0 := by sorry
