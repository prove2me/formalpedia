-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_eq271_fractile_index
-- name    : AVRideHail.MonopolyCapacity.eq271_fractile_index
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:35.337994+00:00
-- url     : https://prove2.me/theorems/730b78da-90cf-4860-81bb-10e05eae1208
-- title:
--   (271), pp. 87–88 — a unique K with Σ_{i>K} P(m_i) < c ≤ Σ_{i≥K} P(m_i), and it is the smallest i with Σ_{>i} < c
-- statement:
--   Let $I \ge 1$ and let $P(m_1), \dots, P(m_I) \ge 0$ be probabilities summing to $1$. Let $0 < c < 1$ (in the application, $c$ is the critical fractile $c_f/(w_0 - c_v)$, which lies in $(0,1)$ by Assumption 1). Then:
--   1. there is exactly one index $K$ with
--   $$\sum_{i=K+1}^I P(m_i) < c \le \sum_{i=K}^I P(m_i);$$
--   2. the smallest index $K$ with $\sum_{i=K+1}^I P(m_i) < c$ satisfies this double inequality.
--
--   This is the discrete critical-fractile condition that identifies the optimal capacity index of Proposition 8.
--
--   **Formalization Note.** Indices are 0-based (`Fin I`): $\sum_{i=K+1}^I$ is the sum over indices strictly above $K$ and $\sum_{i=K}^I$ over indices at least $K$. Uniqueness is proved on the page from "$\sum_{i=K}^I P(m_i)$ is strictly decreasing in $K$", which needs positive masses; the statement assumes only $P(m_i) \ge 0$, under which uniqueness still holds.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), pp. 87–88, (271), App. E.1.3

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem eq271_fractile_index (I : ℕ) (hI : 0 < I) (prob : Fin I → ℝ)
    (hprob : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∃! K : Fin I, ∑ j ∈ Finset.Ioi K, prob j < c ∧ c ≤ ∑ j ∈ Finset.Ici K, prob j) ∧
      ∀ K : Fin I, IsLeast {k : Fin I | ∑ j ∈ Finset.Ioi k, prob j < c} K →
        (∑ j ∈ Finset.Ioi K, prob j < c ∧ c ≤ ∑ j ∈ Finset.Ici K, prob j) := by sorry

end AVRideHail.MonopolyCapacity
