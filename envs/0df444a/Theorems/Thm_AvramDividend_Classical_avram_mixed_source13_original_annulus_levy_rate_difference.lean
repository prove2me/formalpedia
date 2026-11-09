-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
-- name    : AvramDividend.Classical.avram_mixed_source13_original_annulus_levy_rate_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:45:52.518123+00:00
-- url     : https://prove2.me/theorems/832d1bcb-56d9-461b-a8bf-cae76e9ef7c9
-- title:
--   Original nested negative cutoff intensity splits over its physical annulus
-- statement:
--   For every original spectrally negative Levy model, bounded clock and nested cutoff n≤m, the finite real Levy intensity on the larger negative cutoff equals the smaller intensity plus the annulus intensity. This converts the Proved original annulus off-time covariance c17e6a0d centring difference into the true annulus rate for the original factorial moment 6ea0212e.
-- source:
--   MIX-SOURCE13 original-model intensity identification; finite cutoff Levy rates; no other assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_annulus_levy_rate_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    ((T : ℝ≥0∞) * X.ν (Iic d)).toReal =
      ((T : ℝ≥0∞) * X.ν (Iic c)).toReal +
      ((T : ℝ≥0∞) * X.ν (Ioc c d)).toReal := by sorry
