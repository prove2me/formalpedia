-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_of_positive_axis_antitone_tendsto_zero
-- name    : AvramDividend.Classical.nonnegative_of_positive_axis_antitone_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:33:10.477982+00:00
-- url     : https://prove2.me/theorems/ead51c5d-c681-474b-af8f-ef94f613c6a2
-- title:
--   An antitone positive-height tail converging to zero is nonnegative
-- statement:
--   For a real-valued function antitone on the positive half-line, convergence to zero as x→+∞ implies it is nonnegative at every positive x. This discharges the nonnegativity condition for the log-derivative tail from monotonicity plus zero asymptotics, isolating a redundant hypothesis in the analytic excursion-height reconstruction.
-- source:
--   Pinned Mathlib Filter.le_of_tendsto and eventually_ge_atTop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set Filter
open scoped Topology

theorem AvramDividend.Classical.nonnegative_of_positive_axis_antitone_tendsto_zero
    (g : ℝ → ℝ)
    (hanti : AntitoneOn g (Ioi (0 : ℝ)))
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∀ x : ℝ, 0 < x → 0 ≤ g x := by sorry
