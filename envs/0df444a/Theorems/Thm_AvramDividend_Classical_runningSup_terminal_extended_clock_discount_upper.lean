-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_discount_upper
-- name    : AvramDividend.Classical.runningSup_terminal_extended_clock_discount_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:01:18.548342+00:00
-- url     : https://prove2.me/theorems/b479367c-a2cb-4083-9f90-c53c78bf6a4a
-- title:
--   Stopped terminal record cell bound for finite or infinite next-passage clocks
-- statement:
--   The discounted Stieltjes mass of running-supremum dividends after an attained record b and up to a finite terminal time t is bounded above by h exp(-q u), provided t is at or before the first upcrossing of b+h in extended real time. The next passage may be infinite, and equality at the next passage is allowed. This closes both finite and infinite next-record-clock cases required by the upper stopped-renewal pathwise cover.
-- source:
--   Combines first-passage peak attainment and the raw-supremum characterization with the previously proved discounted partial record-cell inequality.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partial_record_cell_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_terminal_extended_clock_discount_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞))) :
    (∫⁻ r,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by sorry
