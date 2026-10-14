-- Prove2me | Theorems.Thm_ClassicalSecretary_exists_optimal_cutoffRule
-- name    : ClassicalSecretary.exists_optimal_cutoffRule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:51:44.328059+00:00
-- url     : https://prove2.me/theorems/3dbd7c77-8631-46ca-af13-aa0751fe1e2d
-- title:
--   An optimal stopping rule is a cutoff rule
-- statement:
--   Let $n \ge 1$. Among all stopping rules that depend only on the relative ranks seen so far, some cutoff rule is optimal: there is $r$ with $1 \le r \le n$ such that
--   $$P_n(\text{cutoff } r) = V_n = \sup_s P_n(s).$$
--
--   This reduces the optimization over all rank-based rules to a one-parameter family.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy", first paragraph: "It can be shown that the optimal strategy lies in this class of strategies"; History section (Palermo's appendix to Flood's 1958 letter).

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem exists_optimal_cutoffRule (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ n ∧ successProb n (cutoffRule r) = optimalProb n := by sorry

end ClassicalSecretary
