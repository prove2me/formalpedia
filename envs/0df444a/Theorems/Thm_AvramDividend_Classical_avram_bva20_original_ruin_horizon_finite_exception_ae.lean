-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_original_ruin_horizon_finite_exception_ae
-- name    : AvramDividend.Classical.avram_bva20_original_ruin_horizon_finite_exception_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:51:24.315511+00:00
-- url     : https://prove2.me/theorems/6aaf18d7-21c1-4d4b-9e83-a20ef05a8ed3
-- title:
--   Time zero, physical horizon and ruin endpoint form a real-Lebesgue null exceptional set
-- statement:
--   For any real horizon and finite ruin time, almost every physical real time differs from zero, the horizon and the ruin endpoint. Those are the only excluded contact instants when combining original pre-ruin and post-ruin grid mask pointwise convergence with the inner-horizon truncation for 7ccc2a1a. The result applies equally if T or the ruin parameter coincides with zero, since their union remains finite and Lebesgue-null.
-- source:
--   Boundary exceptional-set a.e. predicate for original stopped compensator DCT in 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_original_ruin_horizon_finite_exception_ae
    (T τ : ℝ) :
    ∀ᵐ t : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ≠ 0 ∧ t ≠ T ∧ t ≠ τ := by sorry
