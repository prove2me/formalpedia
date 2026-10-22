-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_tendsto_of_uniform_truncation_approximations
-- name    : AvramDividend.Classical.chat03_tendsto_of_uniform_truncation_approximations
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:04:13.062807+00:00
-- url     : https://prove2.me/theorems/2596f809-b6f2-49e3-bdab-ca77f59e7393
-- title:
--   Convergence from uniformly accurate truncation approximations
-- statement:
--   In a pseudometric space, a sequence converges if for every accuracy there exists a positive truncation scale such that the original sequence is uniformly close to a convergent truncated sequence and the corresponding truncated limit is equally close to the desired limit. The proof is the metric triangle inequality with three equal error allocations.
-- source:
--   Metric.tendsto_atTop and the triangle inequality.

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

open Filter Topology

theorem AvramDividend.Classical.chat03_tendsto_of_uniform_truncation_approximations
    {α : Type*} [PseudoMetricSpace α]
    (a : ℕ → α) (b : ℝ → ℕ → α) (L : α) (B : ℝ → α)
    (hconv : ∀ R > 0, Tendsto (b R) atTop (𝓝 (B R)))
    (happrox : ∀ ε > 0, ∃ R > 0,
      (∀ n, dist (a n) (b R n) ≤ ε) ∧ dist (B R) L ≤ ε) :
    Tendsto a atTop (𝓝 L) := by sorry
