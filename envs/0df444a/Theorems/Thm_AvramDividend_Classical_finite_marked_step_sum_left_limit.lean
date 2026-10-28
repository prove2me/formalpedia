-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_marked_step_sum_left_limit
-- name    : AvramDividend.Classical.finite_marked_step_sum_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:48:35.479972+00:00
-- url     : https://prove2.me/theorems/b48f5f1e-fb15-446a-8f79-42c706f7fd83
-- title:
--   A finite sum of marked right-continuous jump steps has an exact left limit obtained by excluding marks at the current time
-- statement:
--   Given finitely many marked times tau_i≥0 and real weights w_i, define a right-continuous step path F(s)=Σ_{i∈S} (if tau_i≤s then w_i else 0). At every t≥0 the limit from strictly earlier times equals Σ_{i∈S} (if tau_i<t then w_i else 0). The theorem also handles simultaneous marked times exactly: all marks with tau_i=t are excluded from the left limit. It is the deterministic jump-path identity needed to identify canonical finite-band Poisson marks with càdlàg process jumps before passing through the compensated infinite-annulus limit.
-- source:
--   LeanLevy/RandomMeasure/LevyJumpPath.lean defines finite bandStepFinsetSum as sums of right-continuous marked steps; Mathlib tendsto_finsetSum and one-sided neighbourhoods.

import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter Set Topology
open scoped NNReal BigOperators

theorem AvramDividend.Classical.finite_marked_step_sum_left_limit
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ) (t : ℝ≥0) :
    Tendsto
      (fun s : ℝ≥0 => ∑ i ∈ S, if τ i ≤ s then w i else 0)
      (nhdsWithin t (Iio t))
      (nhds (∑ i ∈ S, if τ i < t then w i else 0)) := by sorry
