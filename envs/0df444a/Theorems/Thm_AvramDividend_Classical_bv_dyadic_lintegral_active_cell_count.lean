-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_dyadic_lintegral_active_cell_count
-- name    : AvramDividend.Classical.bv_dyadic_lintegral_active_cell_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:57:08.445598+00:00
-- url     : https://prove2.me/theorems/a0729c72-a45d-44ed-a7a5-bbf1489aaca9
-- title:
--   bv dyadic lintegral active cell count
-- statement:
--   Linearity of expected active-cell count without independence: the nonnegative Lebesgue integral of the sum of N measurable indicator functions equals the sum of the N event probabilities. This is the critical Tonelli-style step for dyadic finite-activity residual increment counting. Uses Mathlib's lintegral_finsetSum and lintegral_indicator_one.
-- source:
--   Avram Palmowski Pistorius (2007) first-jump branch; Mathlib finite sums and Lebesgue integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Finset
open scoped ENNReal

theorem AvramDividend.Classical.bv_dyadic_lintegral_active_cell_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (N : ℕ)
    (hE : ∀ i : ℕ, i < N → MeasurableSet (E i)) :
    (∫⁻ ω, ∑ i ∈ Finset.range N,
      (E i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) =
      ∑ i ∈ Finset.range N, P (E i) := by sorry
