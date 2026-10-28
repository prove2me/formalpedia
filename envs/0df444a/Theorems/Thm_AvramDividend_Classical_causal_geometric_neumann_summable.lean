-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_summable
-- name    : AvramDividend.Classical.causal_geometric_neumann_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:44:07.628627+00:00
-- url     : https://prove2.me/theorems/e4d15e3a-c84b-48a0-83ff-bd683aae5377
-- title:
--   Pointwise geometric bounds imply summability of the Gaussian Neumann expansion
-- statement:
--   Every real-valued Neumann correction family geometrically bounded at a fixed time x defines a summable infinite series, with no additional positivity assumption on its coefficients.
-- source:
--   Apply the proved Mathlib geometric series summability criterion and the exact Summable.of_norm_bounded comparison lemma. The canonical Gaussian C1 Neumann construction has geometric per-term bounds; this proves the summability input from which tendsto_sum_tsum_nat gives convergence of finite sums in causal_neumann_resolvent_dominated_convergence.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Exponential

theorem AvramDividend.Classical.causal_geometric_neumann_summable
    (Q : ℕ → ℝ → ℝ) (ρ x : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hQ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n) :
    Summable (fun n : ℕ => Q n x) := by sorry
