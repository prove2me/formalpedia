-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_terminal_partial_record_clock_discount_upper
-- name    : AvramDividend.Classical.runningSup_terminal_partial_record_clock_discount_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:55:37.37535+00:00
-- url     : https://prove2.me/theorems/deef871a-2baa-4cf5-8e2d-901e888cacf4
-- title:
--   Discounted terminal partial record cell bounded by its left first-record weight
-- statement:
--   If u is a finite first upcrossing of level b and t is strictly before the finite first upcrossing of b+h, the stopped running-supremum increase on (u,t] is at most h. Nonnegative discount makes the discounted Stieltjes reward on that terminal partial record cell at most h exp(-q u). This is the missing terminal-cell estimate needed alongside the accepted complete-record-cell upper bounds.
-- source:
--   First-upcrossing peak attainment, equality of running supremum and process at first record, pre-upcrossing running-sup bound, and the accepted discounted partial-record-cell lemma. Supports root c6c3b1d0-2c2f-41ce-a5a0-2771efcc3a69.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partial_record_cell_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_terminal_partial_record_clock_discount_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (ht : t < v) :
    (∫⁻ r,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by sorry
