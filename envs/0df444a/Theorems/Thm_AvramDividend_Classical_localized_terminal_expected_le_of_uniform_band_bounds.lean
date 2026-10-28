-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_terminal_expected_le_of_uniform_band_bounds
-- name    : AvramDividend.Classical.localized_terminal_expected_le_of_uniform_band_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:37:33.138625+00:00
-- url     : https://prove2.me/theorems/5ee8a0e0-5139-4012-b309-93b68007939c
-- title:
--   Uniform finite reserve-band HJB terminal estimates imply the full unbounded-reserve expectation bound
-- statement:
--   For a measurable reserve, survival event and HJB test, if every integer reserve-band truncation has terminal expectation at most K, then the unrestricted nonnegative-reserve terminal expectation is also at most K. This is the exact order-theoretic upper-bound transfer needed for an infinite strategy cap after localisation of a stochastic verification inequality.
-- source:
--   Immediate iSup elimination from the independent monotone convergence identity localized_nonnegative_terminal_lintegral_iSup_bands.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_localized_nonnegative_terminal_lintegral_iSup_bands

open MeasureTheory Set
open scoped Classical ENNReal

theorem AvramDividend.Classical.localized_terminal_expected_le_of_uniform_band_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (r : Ω → ℝ) (hr : Measurable r)
    (w : ℝ → ℝ) (hw : Measurable w)
    (K : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω ∧ r ω ≤ (n : ℝ) then
        ENNReal.ofReal (w (r ω)) else 0 ∂P) ≤ K) :
    (∫⁻ ω, if ω ∈ A ∧ 0 ≤ r ω then
      ENNReal.ofReal (w (r ω)) else 0 ∂P) ≤ K := by sorry
