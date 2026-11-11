-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_physical_positive_error_squeeze
-- name    : AvramDividend.Classical.avram_bva21_physical_positive_error_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:12:45.750989+00:00
-- url     : https://prove2.me/theorems/0528a35e-e853-4e2f-ab0c-2410b1d16286
-- title:
--   Vanishing positive physical error from a nonnegative vanishing ledger envelope
-- statement:
--   Analytic closure for the original BV finite-jump physical cash ledger: when its signed cash-minus-compensated-source error is bounded above pointwise by an explicitly nonnegative remainder tending to zero, the required positive part tends to zero. This is the precise squeeze step needed after deriving a source-exact Taylor, ruin-contact and collision bound in 6ce6d0c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva21_physical_positive_error_squeeze
    (E err : ℕ → ℝ)
    (hBound : ∀ n, E n ≤ err n)
    (hErrNonneg : ∀ n, 0 ≤ err n)
    (hErr : Tendsto err atTop (𝓝 0)) :
    Tendsto (fun n => max (E n) 0) atTop (𝓝 0) := by sorry
