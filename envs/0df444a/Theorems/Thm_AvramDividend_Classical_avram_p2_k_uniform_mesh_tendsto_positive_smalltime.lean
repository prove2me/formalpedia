-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_k_uniform_mesh_tendsto_positive_smalltime
-- name    : AvramDividend.Classical.avram_p2_k_uniform_mesh_tendsto_positive_smalltime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:05:54.513662+00:00
-- url     : https://prove2.me/theorems/c72a855a-7124-4892-ac6b-c664bf097f5f
-- title:
--   Fixed-horizon uniform Lévy mesh tends to zero through positive times
-- statement:
--   For every strictly positive real horizon T, the original uniform-mesh cell width T/(n+1) approaches zero from the positive side. The lemma supplies the exact filter convergence side condition for substituting a source small-time Lévy expectation rate into the stationary uniform-grid identity, without any stochastic intensity or alternative process assumptions.
-- source:
--   Pinned Mathlib tendsto_natCast_atTop_atTop, Filter.tendsto_atTop_add_const_right, tendsto_inv_atTop_zero and tendsto_nhdsWithin_iff. The parent bridge avram_p2_k_rate_uniform_grid_algebra_bridge expects precisely this convergence for the genuine T/(n+1) grid used by P2-A's proved stationary expectation identity 3c63c970-b4e9-4f60-aae9-0b636f46bb61.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.NhdsWithin

open Filter Topology Set

theorem AvramDividend.Classical.avram_p2_k_uniform_mesh_tendsto_positive_smalltime
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop
      (nhdsWithin (0 : ℝ) (Ioi 0)) := by sorry
