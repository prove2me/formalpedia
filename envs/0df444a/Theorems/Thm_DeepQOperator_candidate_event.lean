-- Prove2me | Theorems.Thm_DeepQOperator_candidate_event
-- name    : DeepQOperator.candidate_event
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:07.512202+00:00
-- url     : https://prove2.me/theorems/341f534e-4f6c-40f9-91f3-d4f57c036c22
-- title:
--   The candidate event: on $G$, $|J|\le64$ and the restricted maxima are $A$ and $B$
-- statement:
--   Let $m\ge2$, $\theta\in P_{cb}$, and let $\widetilde b\in\mathbb R^m$ satisfy $\|\widetilde b-b\|_\infty\le1/16$. Put $J=\{i:\widetilde b_i\ge1/8\}$. Then every $i$ with $b_i>3/16$ is in $J$; every $i\in J$ has $b_i\ge1/16$, so
--   $$\frac{|J|}{256}\le\sum_{i\in J}b_i^2\le\frac14,\qquad |J|\le64;$$
--   every excluded index has $b_i<3/16$; and the maxima restricted to $J$ with their floors retained are exactly $A$ and $B$ (also for empty $J$, floor ties, and several maximizers).
--
--   This shows that on the success event the overflow cutoff of Theorem 2's protocol is never used and the candidate replies determine both maxima.
--
--   Differences from the source:
--   - generalization: on the event G of the sampling seed → for every vector b̃ with ∥b̃ − b∥_∞ ≤ 1/16; reason: G is exactly this condition on the estimate
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.3, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator

/-- **The candidate event** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.3, p.25, PDF p.28).

Let `θ ∈ P_cb` and let `b̃` be any estimate with `∥b̃ - b∥_∞ ≤ 1/16` (the event `G`). Put
`J = {i : b̃_i ≥ 1/8}`. Then every `i` with `b_i > 3/16` is in `J`; every `i ∈ J` has `b_i ≥ 1/16`, so
`|J|/256 ≤ Σ_{i∈J} b_i² ≤ 1/4` and `|J| ≤ 64`; every excluded index has `b_i < 3/16`; and the exact
maxima restricted to `J`, with their floors retained, are exactly `A` and `B`.

**Formalization Note.** The estimate is an arbitrary vector `b̃ : Fin m → ℝ`; the statement is
deterministic. Restricted maxima are `rowAOn`, `rowBOn` (floor `1/4` kept, so an empty `J` is covered). -/
theorem candidate_event (m : ℕ) (hm : 2 ≤ m) (θ : Coord m → ℝ) (hθ : θ ∈ Pcb m)
    (bt : Fin m → ℝ) (hbt : ∀ i, |bt i - bScore m i θ| ≤ 1 / 16) :
    (∀ i, 3 / 16 < bScore m i θ → i ∈ univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i)) ∧
    (∀ i ∈ univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i), 1 / 16 ≤ bScore m i θ) ∧
    ((univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i)).card : ℝ) / 256 ≤
      ∑ i ∈ univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i), bScore m i θ ^ 2 ∧
    ∑ i ∈ univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i), bScore m i θ ^ 2 ≤ 1 / 4 ∧
    (univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i)).card ≤ 64 ∧
    (∀ i, i ∉ univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i) → bScore m i θ < 3 / 16) ∧
    rowAOn m (univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i)) θ = rowA m θ ∧
    rowBOn m (univ.filter (fun i => (1 / 8 : ℝ) ≤ bt i)) θ = rowB m θ := by sorry

end DeepQOperator
