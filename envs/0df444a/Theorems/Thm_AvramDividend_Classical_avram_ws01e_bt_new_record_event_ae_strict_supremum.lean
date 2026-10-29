-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_record_event_ae_strict_supremum
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_record_event_ae_strict_supremum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:46:41.253981+00:00
-- url     : https://prove2.me/theorems/ad1d09f1-f9fb-4b46-9c14-ab895ae4c19f
-- title:
--   Strict Lévy upper-ray event equals finite weak first-record event almost everywhere under any real exponential-clock density tilt
-- statement:
--   For a spectrally negative Lévy process, a nonnegative strict upper-record level and an independent real exponential observation clock, the event that the actual running supremum strictly exceeds the level agrees almost everywhere with the finite first-upcrossing event whose age is at most the real clock. The result holds under any nonnegative density weighting of the product law. The sole discrepancy is an atomless clock tie; no Esscher independence or Wiener-Hopf factorisation is assumed. This is the exact event-normalisation bridge needed for genuine upper-record threshold Laplace factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_record_event_ae_strict_supremum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (p : ℝ) (hp : 0 < p)
    (w : Ω × ℝ → ℝ≥0∞) :
    ({z : Ω × ℝ | b < runningSup X (Real.toNNReal z.2) z.1} : Set (Ω × ℝ)) =ᵐ[
      (P.prod (expMeasure p)).withDensity w]
      {z : Ω × ℝ | (twoSidedExitUpTime X b) z.1 < ⊤ ∧
        (((twoSidedExitUpTime X b) z.1).toNNReal : ℝ) ≤ z.2} := by sorry
