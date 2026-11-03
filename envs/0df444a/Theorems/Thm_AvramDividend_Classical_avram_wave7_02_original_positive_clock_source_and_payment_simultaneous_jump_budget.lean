-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:49:43.045812+00:00
-- url     : https://prove2.me/theorems/1e75d817-7fa3-4e6d-8b36-7988d3c9c52a
-- title:
--   Exact original BV/UBV simultaneous negative source jump and right dividend payment produces nonpositive HJB payment correction
-- statement:
--   For the actual spectrally negative Levy source and the original right-dividend controlled reserve at a strictly positive pre-ruin time, the exact combined reserve jump is source mark minus right dividend payment. The canonical positive-cap verification hjump condition proves the total simultaneous value jump plus actual dividend atom is bounded by the source-only value jump. Keeps the true left-limit source, before-source and postpayment reserves and excludes the separate time-zero atom; there are no synthetic processes or independence assumptions.
-- source:
--   Canonical Wave7 BV hjump and literal original riskProcess X x D and rightLimit D, algebraic exact chronological decomposition of simultaneous source/right-payment jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    (w (x + X.X t ω - rightLimit D t ω) -
      w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) +
      (rightLimit D t ω - D t ω) ≤
        w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)) ∧
    ((x + X.X t ω - rightLimit D t ω) -
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) =
      (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) -
        (rightLimit D t ω - D t ω)) := by sorry
