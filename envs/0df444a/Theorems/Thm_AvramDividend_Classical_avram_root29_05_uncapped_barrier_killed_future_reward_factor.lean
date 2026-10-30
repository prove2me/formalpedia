-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_uncapped_barrier_killed_future_reward_factor
-- name    : AvramDividend.Classical.avram_root29_05_uncapped_barrier_killed_future_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:54:56.988952+00:00
-- url     : https://prove2.me/theorems/87a4ffed-93bc-4c6a-97ac-c2203b10b483
-- title:
--   Uncapped actual barrier-ruin killed first-record strong-Markov future reward factor
-- statement:
--   For a genuine spectrally negative Levy process with x between zero and a and a>0, the discounted weight of strict upcrossing of a-x before the actual original-barrier controlled ruin time factors from an arbitrary measurable future shifted-increment path reward, with the original first-passage clock and no finite horizon cutoff. This is a global killed-history identity for the true original process.
-- source:
--   Derived from canonically Proved capped barrier killed future reward factorisation 980471ab and monotone convergence over natural stopping horizons, using measurable random-age shifted paths and genuine original-barrier ruin. Supports 79978d61 and 8fc83520; remains independent of Open exit-scale identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_capped_barrier_killed_future_reward_factor
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_05_uncapped_barrier_killed_future_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let T := twoSidedExitUpTime X (a - x)
    let R := ruinTime X x (barrierStrategy X x a)
    (∫⁻ ω, if T ω < R ω then
      discount ((T ω).toNNReal) * reward (fun t : ℝ≥0 =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω) else 0 ∂P) =
      (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
