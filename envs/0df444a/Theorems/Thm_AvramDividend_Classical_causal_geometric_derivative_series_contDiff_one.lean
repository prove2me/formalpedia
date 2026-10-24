-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_derivative_series_contDiff_one
-- name    : AvramDividend.Classical.causal_geometric_derivative_series_contDiff_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:06:06.946775+00:00
-- url     : https://prove2.me/theorems/70eb7d04-49cd-4ef8-9c8e-2ccd5096f1a4
-- title:
--   C1 regularity of a locally geometrically dominated Neumann series
-- statement:
--   For a series of real differentiable terms on an open interval, continuous term derivatives and a common geometric majorant C r^n with 0≤r<1 imply the sum is C1 there, provided the original series is summable at one interior point. This is the exact local regularity principle needed for a Volterra resolvent series.
-- source:
--   Combines the proved termwise derivative lemma with Mathlib uniform convergence for continuous derivative series.

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Theorems.Thm_AvramDividend_Classical_causal_geometric_derivative_series_hasDerivAt_on_Ioo

open Set

theorem AvramDividend.Classical.causal_geometric_derivative_series_contDiff_one
    (g g' : ℕ → ℝ → ℝ) (a b C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n y, y ∈ Ioo a b → HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n, ContinuousOn (g' n) (Ioo a b))
    (hbound : ∀ n y, y ∈ Ioo a b → ‖g' n y‖ ≤ C * r ^ n)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo a b)
    (hval : Summable fun n => g n y₀) :
    ContDiffOn ℝ 1 (fun y => ∑' n, g n y) (Ioo a b) := by sorry
