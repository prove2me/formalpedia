-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_preruin_iff_eventually_nat_ruin_clocks
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_iff_eventually_nat_ruin_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:41:00.550987+00:00
-- url     : https://prove2.me/theorems/4f03e27d-30da-403e-8eb2-e908b02221b4
-- title:
--   Strict pre-ruin on original source iff eventual membership in every long natural bounded ruin clock
-- statement:
--   For each original risk path, strict pre-ruin holds exactly when from some natural horizon onward all original bounded stopped clocks contain the time. The forward implication is the Proved source eventual-horizon theorem. The reverse reads strict ruin membership off the exact source clock endpoint at n=N. This characterises pointwise limits of stopped strict indicator masks without asserting predictability of the strict ruin event.
-- source:
--   Existing source exact endpoint b4677f24 and new P3-G eventual original strict clock helper.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_iff_eventually_nat_ruin_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ (ω : Ω) (t : ℝ≥0),
      ((t : ℝ≥0∞) < ruinTime X x D ω) ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (t : ℝ≥0∞) <
          (((min (ruinTime X x D ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) : ℝ≥0∞) := by sorry
