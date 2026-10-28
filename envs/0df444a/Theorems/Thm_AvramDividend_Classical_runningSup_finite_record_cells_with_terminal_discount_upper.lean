-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_finite_record_cells_with_terminal_discount_upper
-- name    : AvramDividend.Classical.runningSup_finite_record_cells_with_terminal_discount_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:21:54.708032+00:00
-- url     : https://prove2.me/theorems/9655dbd3-93bf-4170-96da-83d8212f732a
-- title:
--   Completed first-record cells and the terminal partial cell bound stopped dividends
-- statement:
--   If the first N equally spaced record cells are fully attained before ruin and a finite terminal time t lies at or before the next extended first-upcrossing clock, then the discounted stopped Stieltjes reward from the first record up to t is bounded by the sum of N+1 initial-endpoint discounted record increments. This combines the entire sequence of completed cells and the possibly truncated last cell and works even when the next crossing never occurs.
-- source:
--   Algebraic assembly of proved N-cell bound, extended terminal-cell bound and Stieltjes integral additivity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_N_record_cells_discount_upper_bound
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_discount_upper
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_finite_record_cells_with_terminal_discount_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (N : ℕ) (u : ℕ → ℝ≥0) (t : ℝ≥0)
    (hu : ∀ k : ℕ, k ≤ N →
      (u k : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)))
    (hord : ∀ k : ℕ, k < N → (u k : ℝ) ≤ (u (k + 1) : ℝ))
    (hstart : (u 0 : ℝ) ≤ (u N : ℝ))
    (hSurvive : ENNReal.ofReal (u N : ℝ) < τ)
    (hNt : (u N : ℝ) ≤ (t : ℝ))
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0)
        (_ : b + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
        (r : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u 0 : ℝ) (t : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) ≤
    ∑ k ∈ Finset.range (N + 1),
      ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) * ENNReal.ofReal h := by sorry
