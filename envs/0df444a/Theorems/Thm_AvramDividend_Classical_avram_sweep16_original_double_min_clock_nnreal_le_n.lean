-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_nnreal_le_n
-- name    : AvramDividend.Classical.avram_sweep16_original_double_min_clock_nnreal_le_n
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:27:55.525007+00:00
-- url     : https://prove2.me/theorems/81cdc703-bd9b-4e1b-9034-d5b4879b43c5
-- title:
--   Every exact doubly stopped NNReal physical ruin clock is bounded by the finite natural horizon n
-- statement:
--   The original natural ruin/physical localiser double minimum is never top and is bounded above by n in WithTop NNReal. Apply the verified exact coercion and cast the extended-real inequality back to the literal NNReal clock bound. This makes the real boundedness needed by conditional original stopped Ito expectations explicit, preserving the same source clock.
-- source:
--   Proved/public physical extended-clock bounds aceb77c2.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_literal_extended_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_double_min_clock_nnreal_le_n
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (S : ℕ → Ω → ℝ≥0∞) :
    ∀ k ω,
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞))
        (S k ω)).toNNReal ≤ (n : ℝ≥0) := by sorry
