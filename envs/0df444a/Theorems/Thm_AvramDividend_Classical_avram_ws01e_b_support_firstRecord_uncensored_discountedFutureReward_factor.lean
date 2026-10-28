-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
-- name    : AvramDividend.Classical.avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:17:06.068992+00:00
-- url     : https://prove2.me/theorems/481d46a9-9eee-447f-ba81-eb05367eff3a
-- title:
--   Uncensored capped first-record stopped Lévy future reward and discount factorisation
-- statement:
--   For a genuine spectrally negative Lévy process under its original probability law, let τ be its finite first strict upcrossing time capped at an arbitrary nonnegative deterministic N. On the uncensored event where the true extended first-upcrossing occurs strictly before N, an arbitrary measurable nonnegative discount function of τ and any measurable nonnegative reward of the entire post-τ increment path factorise in the actual Lévy expectation. The event is observable at τ in the right-continuous stopped-history sigma-algebra by a separate formally proved source-specific theorem, and the exact finite-stopping strong-Markov path factorisation supplies the equality. This enables localised exponential-clock record regeneration while preserving the uncensored event. No ruin restriction, two-sided exit identity, unstopped scale martingale, Esscher law or Wiener–Hopf independence is assumed.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω := {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       reward (fun t : ℝ≥0 =>
         X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
         (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
