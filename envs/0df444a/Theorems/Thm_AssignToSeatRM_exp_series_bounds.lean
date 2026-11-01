-- Prove2me | Theorems.Thm_AssignToSeatRM_exp_series_bounds
-- name    : AssignToSeatRM.exp_series_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:24.238987+00:00
-- url     : https://prove2.me/theorems/287832fc-0da6-4c4f-8b77-57ba6d478adf
-- title:
--   Proof of Theorem 4, p.ec24 — $\sum_{t\ge1}e^{-At^2/\theta}=O(\sqrt\theta)$ and $\sum_{t\ge1}e^{-At}=O(1)$
-- statement:
--   For every $A>0$:
--
--   1. there is $K$ such that for every integer $\theta\ge1$ the series $\sum_{t=1}^\infty e^{-At^2/\theta}$ converges and
--   $$\sum_{t=1}^{\infty}e^{-At^2/\theta}\ \le\ K\sqrt\theta;$$
--   2. the series $\sum_{t=1}^\infty e^{-At}$ converges.
--
--   These are the two estimates that close the proof of Theorem 4: the first turns the Hoeffding tail bounds of (EC.29) into the $O(\sqrt\theta)$ loss in general, the second into the $O(1)$ loss under NEE.
--
--   **Formalization Note** $O(\sqrt\theta)$ is stated with a constant $K$ uniform over $\theta\ge1$; the second series does not depend on $\theta$, so $O(1)$ is its convergence.
--
--   Differences from the source:
--   - encoding: Σ_{t=1}^{+∞} exp(−At²/θ) = O(√θ) → ∃ K, ∀ θ ∈ ℕ, θ ≥ 1 → summable ∧ Σ' ≤ K√θ; reason: O(·) as θ → ∞ over integer θ ≥ 1, with the constant made uniform; the series is finite for each θ
--   - encoding: Σ_{t=1}^{+∞} exp(−At) = O(1) → the series is summable; reason: the series does not depend on θ
--   - encoding: sums from t = 1 → Lean index t + 1 for t : ℕ; reason: Lean convention; same series
-- source:
--   F. Zhu, S. Liu, R. Wang, Z. Wang, Assign-to-Seat: Dynamic Capacity Control for Selling High-Speed Train Tickets, Manufacturing & Service Operations Management (2023), doi:10.1287/msom.2023.1188, proof of Theorem 4, p.ec24 (the two closing remarks)

import Mathlib

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace AssignToSeatRM

/-- **Proof of Theorem 4, p.ec24** (Zhu, Liu, Wang and Wang, *Assign-to-Seat*, MSOM 2023,
doi:10.1287/msom.2023.1188): "for given `A > 0`, `Σ_{t=1}^{+∞} exp(−A t²/θ) = O(√θ)`" and
"for given `A > 0`, `Σ_{t=1}^{+∞} exp(−A t) = O(1)`."

**Formalization Note.** `O(√θ)` is stated uniformly: there is `K` (depending on `A`) with
`Σ_{t ≥ 1} exp(−A t²/θ) ≤ K√θ` for every integer `θ ≥ 1`, the series being summable. The second
series does not depend on `θ`, so `O(1)` is its convergence. The sums start at `t = 1` (the
Lean index is `t + 1`). -/
theorem exp_series_bounds :
    (∀ A : ℝ, 0 < A → ∃ K : ℝ, ∀ θ : ℕ, 1 ≤ θ →
      Summable (fun t : ℕ => Real.exp (-A * ((t : ℝ) + 1) ^ 2 / θ)) ∧
        ∑' t : ℕ, Real.exp (-A * ((t : ℝ) + 1) ^ 2 / θ) ≤ K * Real.sqrt θ) ∧
    (∀ A : ℝ, 0 < A → Summable (fun t : ℕ => Real.exp (-A * ((t : ℝ) + 1)))) := by sorry

end AssignToSeatRM
