-- Prove2me | Theorems.Thm_ClassicalSecretary_successProb_cutoffRule_one
-- name    : ClassicalSecretary.successProb_cutoffRule_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:49:24.970355+00:00
-- url     : https://prove2.me/theorems/0b6999a4-6dac-42e6-95eb-0aca61ceb582
-- title:
--   Cutoff $r=1$ selects the best with probability $1/n$
-- statement:
--   Let $n \ge 1$. The cutoff rule with cutoff $r = 1$ accepts the very first applicant, who is always a candidate. Its success probability is
--   $$P_n(\text{cutoff } 1) = \frac1n .$$
--
--   This is the boundary case $r=1$ of the success-probability formula for cutoff rules, which the general sum does not cover.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy", sentence after the displayed formula for $P(r)$: "in this case the only feasible policy is to select the first applicant, and hence P(1) = 1/n".

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem successProb_cutoffRule_one (n : ℕ) (hn : 1 ≤ n) :
    successProb n (cutoffRule 1) = 1 / (n : ℝ) := by sorry

end ClassicalSecretary
