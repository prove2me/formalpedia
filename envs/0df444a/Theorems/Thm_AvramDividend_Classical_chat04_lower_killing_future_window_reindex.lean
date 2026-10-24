-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_future_window_reindex
-- name    : AvramDividend.Classical.chat04_lower_killing_future_window_reindex
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:53:22.923881+00:00
-- url     : https://prove2.me/theorems/73138feb-c068-4f68-8744-d447aaae8fa3
-- title:
--   Re-index future ruin survival onto the post-observation Lévy increment path
-- statement:
--   The lower-barrier survival event over the original interval s≤v≤u equals survival of the elapsed-time future increment path indexed by 0≤r≤u−s, with the reserve at s as starting point. The equality is exact for every sample path, uses only nonnegative-real time arithmetic, and is the bridge from historical ruin killing to the published full future-path Markov-Tonelli transition law.
-- source:
--   Deterministic time-shift identity of the downward-killed q-scale process in the Avram two-sided exit martingale proof.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_killing_future_window_reindex
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} =
      {ω | ∀ r : ℝ≥0, r ≤ u - s →
        0 ≤ (x + X.X s ω) + (X.X (s + r) ω - X.X s ω)} := by sorry
