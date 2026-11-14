-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
-- name    : AvramDividend.Classical.avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:18:47.15051+00:00
-- url     : https://prove2.me/theorems/4207597e-615a-4ae3-9195-30b6560b1346
-- title:
--   Actual original spectrally negative Lévy jump marks causing genuine stopped negative-reserve ruin are at most one on each sample path
-- statement:
--   Fix the actual original filtered Lévy process X, dividend D and one sample path. Count the real positive source times up to and including the genuine first ruin time at which the actual Lévy increment is a strictly negative jump and the actual post-dividend controlled reserve riskProcess is strictly negative. Prove the extended cardinality of this original stopped negative-mark ruin-crossing time set is at most one. Every such mark time is necessarily the first ruin time itself by the Proved original stopped negative-reserve times subsingleton lemma, so two distinct genuine stopped crossing marks cannot occur. This controls the possible single w(0) boundary jump contribution when handling infinite-activity BV negative marks and positive-ruin C1 verification, preserving original X,D, marks, first ruin, and cap without imposing finite Lévy activity or spatial mesh-rate assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_stopped_genuinely_negative_reserve_times_subsingleton
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_stopped_negative_levy_mark_genuine_ruin_crossing_count_at_most_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ({t : ℝ≥0 |
      0 < t ∧ (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      X.X t ω < Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      riskProcess X x D t ω < 0} : Set ℝ≥0).encard ≤ 1 := by sorry
