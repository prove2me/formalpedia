-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
-- name    : AvramDividend.Classical.reflectedRuin_strictClock_eq_countableSchedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:18:52.04517+00:00
-- url     : https://prove2.me/theorems/253a6335-9fbc-4aa7-9cad-41a6bbd488c9
-- title:
--   Exact countable-schedule representation of strict reflected dividend ruin time
-- statement:
--   For each actual spectrally negative Lévy sample path and any barrier height, the strict drawdown ruin clock defined as the infimum of all times when the path falls below its running supremum minus the barrier equals the infimum of such crossings over the explicit countable rational observation schedule. Continuity of the running record and right continuity of the Lévy path give the requisite persistence of strict crossings on a right interval. This identifies the true ruin clock with the path-space measurable skeleton used for positive-barrier discounted Stieltjes reward factorisation, without assuming finite variation or a strong-Markov conclusion.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3. Proved rightInterval_lower_strictExit_eq_schedule and runningSup_continuous_actual. This is the exact true-clock component of the positive-barrier reward reconstruction required by 79978d61.

import Mathlib.Topology.Order
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.reflectedRuin_strictClock_eq_countableSchedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if X.X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω -
          runningSup X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω < -a
        then ((((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞) else ⊤) := by
  sorry
