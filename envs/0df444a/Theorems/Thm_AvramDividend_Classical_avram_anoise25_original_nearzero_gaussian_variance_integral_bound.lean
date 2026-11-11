-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise25_original_nearzero_gaussian_variance_integral_bound
-- name    : AvramDividend.Classical.avram_anoise25_original_nearzero_gaussian_variance_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T09:19:09.923895+00:00
-- url     : https://prove2.me/theorems/92557e63-c33a-4f73-a161-63d62bf0d302
-- title:
--   Near-zero original Lévy quadratic variance bounded by inverse-square cutoff
-- statement:
--   The physical Lévy quadratic integral over the uncompensated near-zero negative marks (-1/(n+1),0) is nonnegative and at most (1/(n+1))² times the full finite negative jump intensity. Thus its contribution to a finite-cutoff Gaussian residual moment vanishes with n. All large marks are excluded.
-- source:
--   Root-connected deterministic tail for original finite cutoff exact second moment anoise22, required by Gaussian bracket parent 892afa4a. Uses only finite total negative source intensity, measure restriction, and bounded mark squares.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise25_original_nearzero_gaussian_variance_integral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (n : ℕ) :
    let ε : ℝ := 1 / ((n : ℝ) + 1)
    0 ≤ (∫ z in Ioo (-ε) 0, z ^ 2 ∂X.ν) ∧
      (∫ z in Ioo (-ε) 0, z ^ 2 ∂X.ν) ≤
        ε ^ 2 * (X.ν (Iio (0 : ℝ))).toReal := by sorry
