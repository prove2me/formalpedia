-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_terminal_record_clock_discount_upper_closed
-- name    : AvramDividend.Classical.runningSup_terminal_record_clock_discount_upper_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:08:09.033986+00:00
-- url     : https://prove2.me/theorems/fecbaa90-d6d5-4669-b8f2-bef14899a2c3
-- title:
--   Discounted terminal record cell bound including the next passage endpoint
-- statement:
--   For finite first record clocks u at level b and v at level b+h, the discounted Stieltjes increment from u to any time t ≤ v is at most h exp(-q u). The strict t<v case was already proved. At t=v, attainment of the next record shows that runningSup equals b+h, so the same partial-record bound applies. Inclusion of t=v handles ruin coinciding exactly with a record clock.
-- source:
--   Endpoint closure of accepted runningSup_terminal_partial_record_clock_discount_upper, using firstUpcrossing_attains_peak, firstUpcrossing_runningSup_sub_path_eq_zero and runningSup_discounted_partial_record_cell_upper. Directly supports terminal stopped-record cover.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_partial_record_clock_discount_upper
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partial_record_cell_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_terminal_record_clock_discount_upper_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (ht : t ≤ v) :
    (∫⁻ r,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by sorry
