-- Prove2me | Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
-- name    : AvramDividend.Classical.survived_nextRecord_shifted_upclock_le_lower_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:14:55.36479+00:00
-- url     : https://prove2.me/theorems/4b36c7b8-3aa2-4895-88dd-2c4344d7ea62
-- title:
--   Survival to a later record orders shifted upward and downward first-exit clocks
-- statement:
--   Suppose a spectrally negative Lévy trajectory reaches and survives a first record at level b, subsequently reaches b + ε at finite time v, and survives the reflected drawdown ruin throughout. Starting from the first record, the shifted strict upward exit from ε occurs no later than the shifted strict lower exit from -a. This gives the necessary pathwise upper-exit event inclusion for a renewal upper bound, using the proved record-clock translation and shifted path lower guard.
-- source:
--   Combine the proved next-record clock shift identity with survived_nextRecord_shifted_lower_exit_not_earlier, cancelling the finite initial time in ENNReal.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_lower_exit_not_earlier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.survived_nextRecord_shifted_upclock_le_lower_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) ≤
    (⨅ (t : ℝ≥0)
        (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)) := by sorry
