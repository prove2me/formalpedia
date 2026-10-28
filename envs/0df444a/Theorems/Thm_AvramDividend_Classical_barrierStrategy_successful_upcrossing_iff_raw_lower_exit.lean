-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_successful_upcrossing_iff_raw_lower_exit
-- name    : AvramDividend.Classical.barrierStrategy_successful_upcrossing_iff_raw_lower_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:52:24.514446+00:00
-- url     : https://prove2.me/theorems/6883dd6c-a050-4e3b-8839-28515104cfd9
-- title:
--   A finite barrier upcrossing survives controlled ruin exactly when it precedes raw downward exit
-- statement:
--   If a spectrally negative Lévy path first reaches the positive barrier from below at a finite strict upward-passage clock, then that passage precedes the controlled barrier-strategy ruin time if and only if it precedes the raw downward first-exit clock of the initial reserve. Before the upcrossing, raw reserve nonnegativity implies the reflected drawdown remains within the barrier. No positive jumps and right-continuity make the drawdown ruin time strictly later than the attained record. This is the exact successful-event equivalence needed to replace the controlled-ruin indicator in the below-barrier strong-Markov dividend-value factorisation.
-- source:
--   Avram, Palmowski and Pistorius (2007), barrier-strategy strong-Markov upcrossing before ruin. Verified source-faithful bridge for Open theorem 79978d61-9d1f-4b20-b8a5-114797a8e380 using Proved firstUpcrossing_drawdown_survival_sandwich, firstUpcrossing_strictly_before_drawdown_ruin and barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin.

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_eq_min_rawRuin_drawdownRuin
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_survival_sandwich
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_successful_upcrossing_iff_raw_lower_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (u : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ↔
      (u : ℝ≥0∞) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by sorry
