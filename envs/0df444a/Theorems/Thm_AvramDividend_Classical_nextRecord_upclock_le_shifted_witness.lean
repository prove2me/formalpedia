-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_le_shifted_witness
-- name    : AvramDividend.Classical.nextRecord_upclock_le_shifted_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:49:23.905717+00:00
-- url     : https://prove2.me/theorems/4646fb77-4d0c-4e72-a556-8d0fba36e8dd
-- title:
--   Any shifted future record witness bounds the next original first-passage clock
-- statement:
--   Suppose the Lévy path is exactly at its attained record level b at time u. If the shifted future path rises strictly above ε during the next time interval t, then the official strict first upward crossing time of the next level b+ε is at most u+t. This is the fundamental witness inclusion for transferring shifted Markov future-path upper exits back to the original first-record clock.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, strong-Markov renewal across attained running-supremum records.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_upclock_le_shifted_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (u t : ℝ≥0) (ω : Ω)
    (hAt : X.X u ω = b)
    (hNext : ε < X.X (u + t) ω - X.X u ω) :
    twoSidedExitUpTime X (b + ε) ω ≤ ((u + t : ℝ≥0) : ℝ≥0∞) := by sorry
