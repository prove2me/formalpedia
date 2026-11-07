-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
-- name    : AvramDividend.Classical.avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:25:37.828239+00:00
-- url     : https://prove2.me/theorems/ea6c653f-0fbc-4a7b-969c-05bc71745e2a
-- title:
--   Sampled exit index transported to an original right-continuous continuous-time stopping time
-- statement:
--   For the genuine original spectrally negative Lévy process X and its dividend strategy D, define K as the bounded first two-sided grid exit of the post-payment controlled reserve x+X.X(clock k)−rightLimit D(clock k). Assume a nondecreasing deterministic clock ℕ→ℝ≥0 and a discrete filtration H satisfying H k=𝓕.rightCont(clock k). The already proved source grid exit lemma makes ↑K an H-stopping time. The composed actual time ω↦clock(Kω) is then a stopping time of the original source right-continuous filtration 𝓕.rightCont: for any t, its ≤t event is the countable union over k with clock k≤t of the H k-measurable events K≤k, transferred by clock monotonicity. This does not assert that the unsampled continuous-time first exit is a stopping time or that the grid exit times exhaust ruin.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_grid_exit_clock_isStoppingTime_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (clock : ℕ → ℝ≥0) (hclock : Monotone clock)
    (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => (clock (K ω) : WithTop ℝ≥0)) := by sorry
