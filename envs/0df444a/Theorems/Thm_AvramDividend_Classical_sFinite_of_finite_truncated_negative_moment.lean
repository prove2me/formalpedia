-- Prove2me | Theorems.Thm_AvramDividend_Classical_sFinite_of_finite_truncated_negative_moment
-- name    : AvramDividend.Classical.sFinite_of_finite_truncated_negative_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:42:55.611977+00:00
-- url     : https://prove2.me/theorems/29b84cf1-5e5f-40a0-b47a-59c764044326
-- title:
--   Finite truncated negative moment gives an s-finite measure
-- statement:
--   Let ν be carried by (-∞,0). If the integral of min(-y,1) over negative y is finite, then ν is s-finite. Cover the negative half-line by (-∞,-1/(n+1)] and add [0,∞), which has zero ν-mass.
-- source:
--   Pinned Mathlib exists_nat_one_div_lt, MeasureTheory.meas_ge_le_lintegral_div, MeasureTheory.sigmaFinite_of_countable, and the SigmaFinite-to-SFinite instance.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- A measure carried by the negative half-line is s-finite when the truncated negative magnitude has finite integral. -/
theorem sFinite_of_finite_truncated_negative_moment
    (ν : Measure ℝ)
    (hIci : ν (Ici (0 : ℝ)) = 0)
    (hfin : (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min (-y) 1) ∂ν) < ⊤) :
    SFinite ν := by
  sorry

end AvramDividend.Classical
