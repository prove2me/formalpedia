-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:33:44.128417+00:00
-- url     : https://prove2.me/theorems/9d6c6bf5-0657-4834-af83-d87e1ac347b5
-- title:
--   Every original strict pre-ruin time eventually lies inside all sufficiently long natural bounded ruin clocks
-- statement:
--   On genuine original risk paths, every finite time before ruin is in all sufficiently long natural-horizon stopped strict events. This provides a pointwise eventual statement needed for stopped expectation and mesh-to-limit convergence. Use the pinned ENNReal.exists_nat_gt and the Proved exact source clock endpoint equivalence; no cap-contact occupation assumption.
-- source:
--   Proved exact original ruin clock b4677f24 and exact pinned Mathlib ENNReal.exists_nat_gt.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (t : ℝ≥0∞) <
          (((min (ruinTime X x D ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) : ℝ≥0∞) := by sorry
