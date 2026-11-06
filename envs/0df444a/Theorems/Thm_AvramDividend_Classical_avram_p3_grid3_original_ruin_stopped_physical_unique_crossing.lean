-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:52:20.305232+00:00
-- url     : https://prove2.me/theorems/3cd7a72d-552f-4ecd-a2b7-cd34fbad7c02
-- title:
--   At most one true ruin-clamped physical cell can first reach the stopped horizon
-- statement:
--   On the genuine original Levy process and admissible dividend cash path, its ruin-clamped physical clock is monotone. If a cell first hits the stopped time tau from below, no later cell can again first hit tau from below. This isolates the only possible final ruin/horizon crossing cell for subsequent strict pre-ruin Stieltjes grid summation, with cap contact preserved.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ∀ i j : ℕ, i < j →
      u i < τ → u (i + 1) = τ →
      ¬ (u j < τ ∧ u (j + 1) = τ) := by sorry
