-- Prove2me | Theorems.Thm_ClassicalSecretary_exp_neg_one_le_optimalProb
-- name    : ClassicalSecretary.exp_neg_one_le_optimalProb
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:54:32.863164+00:00
-- url     : https://prove2.me/theorems/b0c475d3-a162-4ba2-8862-371463eff265
-- title:
--   The optimal success probability is at least $1/e$ for every $n$
-- statement:
--   For every number of applicants $n \ge 1$,
--   $$V_n = \sup_s P_n(s) \ \ge\ \frac1e .$$
--
--   Together with the goal theorem, this says the optimal success probability never falls below its limit.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, introduction: "It implies that the optimal win probability is always at least 1/e".

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem exp_neg_one_le_optimalProb (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-1) ≤ optimalProb n := by sorry

end ClassicalSecretary
