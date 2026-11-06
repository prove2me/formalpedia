-- Prove2me | Theorems.Thm_BianchiIX_summable_tsum_le_of_halving
-- name    : BianchiIX.summable_tsum_le_of_halving
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:04:56.147992+00:00
-- url     : https://prove2.me/theorems/fc20bfe6-6040-4951-8795-9a3ea87ba819
-- title:
--   The sum of a nonnegative halving sequence
-- statement:
--   If $u_m\geq0$ and $u_{m+1}\leq u_m/2$ for every $m$, then
--   $u$ is summable and $\sum_{m\geq0}u_m\leq2u_0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean#L65-L81

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology

theorem BianchiIX.summable_tsum_le_of_halving {u : ℕ → ℝ} (hu : ∀ m, 0 ≤ u m)
    (hstep : ∀ m, u (m + 1) ≤ (1 / 2) * u m) :
    Summable u ∧ (∑' m, u m) ≤ 2 * u 0 := by sorry
