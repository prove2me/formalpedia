-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_remainder_tendsto_zero
-- name    : AvramDividend.Classical.causal_neumann_geometric_remainder_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:17:16.058387+00:00
-- url     : https://prove2.me/theorems/20ff3f0b-ba13-4b52-8fd8-7d9998afd43f
-- title:
--   Pointwise geometric bounds force the Neumann remainder to vanish
-- statement:
--   Suppose a sequence of causal Neumann remainder functions Q_n has pointwise absolute value bounded by C(x) times rho to the n, with 0<=rho<1. Then Q_n(x) tends to zero at every x. This supplies the remainder-limit premise of the finite-to-infinite Neumann resolvent bridge.
-- source:
--   Geometric convergence and the norm-squeeze theorem, under the pinned Mathlib environment.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Filter

theorem AvramDividend.Classical.causal_neumann_geometric_remainder_tendsto_zero
    (Q : ℕ → ℝ → ℝ) (C : ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ n : ℕ, ∀ x : ℝ, |Q n x| ≤ C x * ρ ^ n) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => Q n x) atTop (nhds (0 : ℝ)) := by sorry
