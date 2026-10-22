-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
-- name    : AvramDividend.Classical.firstUpcrossing_threshold_iInf_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:34:05.692995+00:00
-- url     : https://prove2.me/theorems/4c7a39ae-f280-47fb-91ab-817b588dc9b2
-- title:
--   Original extended-real first-upcrossing clock is monotone in the record level
-- statement:
--   For the original spectrally negative Lévy sample path, the extended-real first strict upward passage time at a larger threshold c is never earlier than the passage time at a smaller threshold b≤c. Both first-passage times are represented by the exact double infimum over nonnegative times and threshold witnesses in the published stochastic definitions; unreachable levels are allowed to have infinite passage time. The proof is elementary order theory because a time witnessing c<X(t) also witnesses b<X(t). This supplies record-clock monotonicity needed for finite-grid and countable inverse-record-level Stieltjes dividend discretisation, removing separate ordering hypotheses from later record h-cell estimates.
-- source:
--   Published firstUpcrossing infimum expression in Definitions.Def_AvramDividend_Classical_ReflectionBarrier; pinned Mathlib order iInf_le and le_iInf.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_threshold_iInf_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b c : ℝ) (hbc : b ≤ c) :
    (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)) ≤
    (⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞)) := by sorry
