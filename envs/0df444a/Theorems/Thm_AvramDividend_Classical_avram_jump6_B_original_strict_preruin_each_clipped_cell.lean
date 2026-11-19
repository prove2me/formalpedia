-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_preruin_each_clipped_cell
-- name    : AvramDividend.Classical.avram_jump6_B_original_strict_preruin_each_clipped_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:35:57.941507+00:00
-- url     : https://prove2.me/theorems/36bb20f6-726b-4201-913f-79c29ffe7ec1
-- title:
--   Original strictly pre-ruin stopped clock passes to every physical mesh cell
-- statement:
--   Every cell endpoint of the original canonical physical grid clipped at an original pre-ruin stopping clock is either zero or remains strictly before the original ruin time. This discharges the exact interval hypothesis of the already Proved full Stieltjes signed-cash inequalities for all cells on the pre-ruin branch and requires no finite-activity or Gaussian simplification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_jump6_B_original_strict_preruin_each_clipped_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (k j i : ℕ) (ω : Ω)
    (hPre : σ k ω = 0 ∨
      (σ k ω : ℝ≥0∞) < ruinTime X x D ω) :
    let v : ℝ≥0 :=
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ k ω)
    v = 0 ∨ (v : ℝ≥0∞) < ruinTime X x D ω := by sorry
