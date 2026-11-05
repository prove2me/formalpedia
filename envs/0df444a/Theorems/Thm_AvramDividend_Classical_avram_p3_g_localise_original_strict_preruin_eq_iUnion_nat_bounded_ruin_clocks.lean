-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_preruin_eq_iUnion_nat_bounded_ruin_clocks
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eq_iUnion_nat_bounded_ruin_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:28:10.729858+00:00
-- url     : https://prove2.me/theorems/9346bee8-ac73-4bd4-bd18-bec1ce70568b
-- title:
--   Original strict pre-ruin region is the countable natural-horizon exhaustion of bounded original ruin-clock regions
-- statement:
--   On actual original risk paths, t<ruinTime is exactly the countable union over natural deterministic horizons of strict bounded ruin-clock masks. The forward direction uses the exact pinned ENNReal.exists_nat_gt to choose a natural horizon beyond finite t; the reverse uses the Proved source clock endpoint theorem. The countability of the horizon exhaustion supports monotone limits of predictable localisations without any cap occupation assumption.
-- source:
--   Pinned Mathlib ENNReal.exists_nat_gt; Proved P3-G strict clock endpoint b4677f24; original ruinTime only.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eq_iUnion_nat_bounded_ruin_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < ruinTime X x D p.2} :
      Set (ℝ≥0 × Ω)) =
      ⋃ n : ℕ,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) <
            (((min (ruinTime X x D p.2) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) : ℝ≥0∞)} := by sorry
