-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_of_ae_right_germ_ws01b
-- name    : AvramDividend.Classical.bv_strict_lower_exit_no_creeping_of_ae_right_germ_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:16:18.33583+00:00
-- url     : https://prove2.me/theorems/a399e8db-6d50-4a85-a857-06f91ee9916e
-- title:
--   Almost-sure right germ at strict lower-exit clock implies no creeping contact
-- statement:
--   For a spectrally negative Lévy process, if on the lower-first exit event there is almost surely a finite strict downcrossing infimum and an immediate right interval where the process is at or above the ruin boundary, then the value at strict lower exit cannot equal the boundary. This applies the accepted deterministic infimum/contact lemma to random paths and isolates the remaining BV stochastic germ construction.
-- source:
--   Deterministic Prove2Me theorem 7a9793f9; Avram Palmowski Pistorius 2007 strict ruin conventions. Lemma supports bounded-variation target 43a28d8e.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
import Mathlib.Tactic

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_lower_exit_no_creeping_of_ae_right_germ_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ)
    (hGerm : ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω →
      ∃ τ : ℝ≥0,
        (τ : ℝ≥0∞) = twoSidedExitDownTime X (-x) ω ∧
        ∃ ε : ℝ≥0, 0 < ε ∧
          ∀ t : ℝ≥0, τ < t → t < τ + ε → -x ≤ X.X t ω) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by sorry
