-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_up_exit_hits_level_of_no_positive_jumps
-- name    : AvramDividend.Classical.two_sided_up_exit_hits_level_of_no_positive_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:31:26.032256+00:00
-- url     : https://prove2.me/theorems/6e7b393d-2238-4378-8d8c-1f20b27c431d
-- title:
--   Upward two-sided exit hits the level exactly in the absence of positive jumps
-- statement:
--   Let X be a spectrally negative Levy process with cadlag paths and no positive jumps, X(0) = 0. For 0 <= x <= a with a > 0, let up-exit be the first passage time above level a - x. If up-exit strictly precedes down-exit below -x, then up-exit is finite and the process is exactly at level a - x at that time: right-continuity forces the value to be at least the level, no-positive-jumps forces it to be at most the level, and the degenerate zero-time case resolves via X(0) = 0 against x <= a. This is the upward boundary-evaluation half (C2-up) of the stopped-scale bridge for the two-sided exit identity.
-- source:
--   Boundary-evaluation half of the H2 bridge: Open 09663d0d (two_sided_exit_stopped_scale_identity) reduces via unfolding to the raw iInf integral closed by Open 3e1ce2c8, whose stochastic core needs (i) the stopped q-harmonic expectation (optional stopping, analytic) and (ii) this exact-hit fact (pure path property of the imported SpectrallyNegativeLevy structure: rightCont, leftLim, noPosJumps, X_zero). Depends only on Definitions modules; no theorem dependencies, hence acyclic. Down-side creeping and the analytic core remain outstanding and are not claimed here.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.two_sided_up_exit_hits_level_of_no_positive_jumps {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) (ω : Ω)
    (hlt : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) = twoSidedExitUpTime X (a - x) ω ∧ X.X t ω = a - x := by
  sorry
