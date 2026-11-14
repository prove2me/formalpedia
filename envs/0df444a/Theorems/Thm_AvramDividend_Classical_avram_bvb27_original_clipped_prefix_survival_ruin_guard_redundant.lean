-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27_original_clipped_prefix_survival_ruin_guard_redundant
-- name    : AvramDividend.Classical.avram_bvb27_original_clipped_prefix_survival_ruin_guard_redundant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:06:06.095044+00:00
-- url     : https://prove2.me/theorems/ad93698c-8a8e-4ee2-bbf7-2cd6692c06ec
-- title:
--   Original survivor physical uniform clipped prefix automatically precedes the true source ruin clock
-- statement:
--   On an original physical path whose actual ruinTime is strictly after the finite observation horizon S, any nonnegative physical clock t inside the exact original clipped uniform prefix T-T/(n+2) is automatically no later than actual ruinTime. This establishes that the true ruin mask inside the original stopped negative-mark K integrand is redundant for all physical times in the original clipped prefix on survival paths, while retaining all of the source marks and the exact terminal time convention.
-- source:
--   Original physical finite-horizon survival branch ed067740 and clipped uniform grid; pinned NNReal and ENNReal order coercion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb27_original_clipped_prefix_survival_ruin_guard_redundant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSurvival : (S : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (t : ℝ≥0)
    (hPrefix : (t : ℝ) < T - T / ((n : ℝ) + 2)) :
    (t : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
