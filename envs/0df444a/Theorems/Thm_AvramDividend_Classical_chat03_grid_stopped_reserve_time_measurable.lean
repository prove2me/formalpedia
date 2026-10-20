-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
-- name    : AvramDividend.Classical.chat03_grid_stopped_reserve_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:13:23.077996+00:00
-- url     : https://prove2.me/theorems/d31b0bab-953d-485e-996e-1452100c91a3
-- title:
--   Stopped Lévy reserve and time are measurable at strict bounded two-sided grid exit
-- statement:
--   For a spectrally negative Lévy process adapted to its original filtration and any deterministic sampled clock, let K be the bounded first strict two-sided grid exit, with above-upper or below-lower events. Then both the sampled reserve X_(clock K) and real-valued sampled time clock K are measurable on the original sample space. Prove this from the exact pinned discrete Adapted.isStoppingTime_hittingBtwn and measurable_stoppedValue theorems; the time itself is a stopped constant-in-omega process. No right-continuous filtration, strong Markov property or continuous-time stopping theorem is used. This discharges the scale-payoff measurability prerequisite for the finite-grid L² bound, using the independently Proved Borel measurability of W.
-- source:
--   Pinned Mathlib Probability.Process.HittingTime and Probability.Process.Stopping, 0df444a360eaa60ab8c11dca51a86af692955474; exact Formalpedia SpectrallyNegativeLevy.adapted and previous Chat 03 strict two-sided grid definitions.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_grid_stopped_reserve_time_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω => X.X (clock (K ω)) ω) ∧
      Measurable (fun ω => (clock (K ω) : ℝ)) := by sorry
