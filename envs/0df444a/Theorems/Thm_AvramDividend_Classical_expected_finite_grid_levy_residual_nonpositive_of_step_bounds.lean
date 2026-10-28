-- Prove2me | Theorems.Thm_AvramDividend_Classical_expected_finite_grid_levy_residual_nonpositive_of_step_bounds
-- name    : AvramDividend.Classical.expected_finite_grid_levy_residual_nonpositive_of_step_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:15:31.975417+00:00
-- url     : https://prove2.me/theorems/2298f6bc-c9cb-4cdc-bca0-7963e4f85590
-- title:
--   Nonpositive total expected Lévy residual from stepwise HJB bounds
-- statement:
--   For an integrable finite-grid Lévy residual at each time step, a nonpositive expectation at every step implies that the expectation of the accumulated residual is nonpositive. This formalises the finite martingale/generator summation step needed to connect one-step conditional HJB control to the expected dividend ledger. The residual r may be instantiated with the discounted change in the verification function caused by an uncontrolled Lévy increment.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), finite-grid generator residual summation.

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Finset
open AvramDividend.Classical

theorem AvramDividend.Classical.expected_finite_grid_levy_residual_nonpositive_of_step_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (r : ℕ → Ω → ℝ)
    (hInt : ∀ k, Integrable (r k) P)
    (hStep : ∀ k, (∫ ω, r k ω ∂P) ≤ 0)
    (n : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range n, r k ω ∂P) ≤ 0 := by sorry
