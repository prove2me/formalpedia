-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_theorem_2_a
-- name    : BundleShaping.NoOrderSet.theorem_2_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:22.991434+00:00
-- url     : https://prove2.me/theorems/df115967-866f-4227-8175-ef44e03ff131
-- title:
--   Theorem 2(a), p. 23 — V_{t+1} is jointly concave and non-increasing
-- statement:
--   In the bundle-to-stock model under the standing assumptions (Property-CV of the revenue rates, $b^p_t\ge 0$, $c^p_t+h_t\ge 0$), for every period $1\le t\le T$ the next-period value function $V_{t+1}:\mathbb R^I\to\mathbb R$ of (9) is
--
--   $$\text{jointly concave on }\mathbb R^I\quad\text{and}\quad\text{non-increasing for the coordinatewise order.}$$
--
--   Concavity of the continuation value is what propagates the joint concavity of $G_t$ backwards through the horizon.
--
--   **Formalization Note.** At $t=T$ the statement is about $V_{T+1}\equiv 0$. The value function is the real supremum of $G_t$ over the feasible set of (9).
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 23, Theorem 2(a)

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem theorem_2_a (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) : ConcaveOn ℝ Set.univ (P.V (t + 1)) ∧ Antitone (P.V (t + 1)) := by sorry

end BundleShaping.NoOrderSet
