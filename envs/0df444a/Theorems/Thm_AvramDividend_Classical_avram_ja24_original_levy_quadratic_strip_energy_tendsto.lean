-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja24_original_levy_quadratic_strip_energy_tendsto
-- name    : AvramDividend.Classical.avram_ja24_original_levy_quadratic_strip_energy_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:16:22.550833+00:00
-- url     : https://prove2.me/theorems/3cd9911c-c39f-4cb4-8ec0-53b7ec40ed62
-- title:
--   Original Levy finite marked-strip quadratic energy converges to omitted tail
-- statement:
--   Under finite negative jump activity, the real quadratic Levy mark integral across a finite negative cutoff strip converges as its upper cutoff approaches zero to the complete omitted-tail quadratic integral.
-- source:
--   J-A24 analytic variance passage e5df71c0 and 892afa4a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja24_original_levy_quadratic_strip_energy_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    Tendsto
      (fun m : ℕ => ∫ z in Ioc
        (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))),
        z ^ 2 ∂X.ν)
      atTop (nhds (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) := by sorry
