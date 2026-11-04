-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_raw_levy_exponential_expected_le_one
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_raw_levy_exponential_expected_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T11:10:35.967141+00:00
-- url     : https://prove2.me/theorems/eb3af3e9-886d-40f9-a5df-e0a7a4393d47
-- title:
--   Original source q-discounted Lévy exponential has mean bounded by one
-- statement:
--   For the actual spectrally negative Lévy source, the q-discounted exponential has expected value at most one at every deterministic time whenever θ≥0 and ψθ≤q. This follows by the existing original source supermartingale bound at zero with X.X 0=0 and probability normalisation. It will be the base estimate in a finite-grid stopping argument; no random-time optional sampling is claimed.
-- source:
--   Original source Lévy exponential supermartingale 9a96f7d0 Proved; X.X_zero; Mathlib Supermartingale.setIntegral_le; X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_discounted_exponential_levy_supermartingale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_raw_levy_exponential_expected_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (t : ℝ≥0) :
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * q) ∂P) ≤ 1 := by sorry
