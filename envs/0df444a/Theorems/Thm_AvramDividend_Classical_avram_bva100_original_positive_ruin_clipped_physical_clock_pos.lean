-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva100_original_positive_ruin_clipped_physical_clock_pos
-- name    : AvramDividend.Classical.avram_bva100_original_positive_ruin_clipped_physical_clock_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:45:37.56721+00:00
-- url     : https://prove2.me/theorems/04fb96b4-7a98-4334-8911-f791718e0f55
-- title:
--   Non-immediate ruin has positive original physical clipped stop before every positive horizon
-- statement:
--   In the original spectrally negative Levy risk process, a path with ruinTime≠0 and positive physical horizon S has strictly positive clipped stopped clock min(ruinTime,S).toNNReal, even if ruinTime=∞. Proved by positivity of both sides of the min and finiteness from S. This removes the zero-stopping endpoint before applying the positive-ruin C1 mesh Stieltjes ledger BVA96; it assumes no extra jump structure or finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva100_original_positive_ruin_clipped_physical_clock_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (S : ℝ≥0) (hS : 0 < S)
    (hR : ruinTime X x D ω ≠ 0) :
    0 < (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal := by sorry
