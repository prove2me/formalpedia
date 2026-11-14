-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
-- name    : AvramDividend.Classical.avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:57:43.999135+00:00
-- url     : https://prove2.me/theorems/8707a8a4-5923-4838-acaa-3f96430ccb5c
-- title:
--   Original stopped path can have at most one genuinely negative controlled reserve observation at or before the first ruin time
-- statement:
--   For the actual original spectrally negative Levy path and any dividend control D, let sigma be the literal first ruin time defined as the infimum of physical times whose genuine riskProcess X x D is strictly negative. Then the set of strictly positive times t no later than sigma at which that actual controlled reserve is strictly negative is a subsingleton. If such a time exists, it must equal sigma by the defining infimum, hence cannot occur twice before the stop. This source-exact one-crossing bound is useful when separating a possible positive w(0) jump-crossing term from the zero-shifted C1 negative-mark remainder: any actually ruined stopped path has at most one genuine negative postpayment observation. No finite jump activity, path continuity, Brownian substitute, stochastic domination or spatial mesh rate is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Set.Subsingleton {t : ℝ≥0 |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        riskProcess X x D t ω < 0} := by sorry
