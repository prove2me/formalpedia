-- Prove2me | Theorems.Thm_ClassicalSecretary_tendsto_optimalProb
-- name    : ClassicalSecretary.tendsto_optimalProb
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:54:57.707131+00:00
-- url     : https://prove2.me/theorems/684646cb-829e-4d2b-8ea4-ac748a7315bc
-- title:
--   The 37% rule: the optimal success probability tends to $1/e$
-- statement:
--   Let $V_n$ be the largest probability, over all stopping rules that use only the relative ranks of the applicants seen so far, of selecting the best of $n$ applicants interviewed in a uniformly random order. Then
--   $$\lim_{n\to\infty} V_n = \frac1e \approx 0.368 .$$
--
--   This is the classical solution of the secretary problem: as the number of applicants grows, the best achievable chance of picking the single best one converges to $1/e$.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy": "the best applicant is selected with probability 1/e" and "The probability of selecting the best applicant in the classical secretary problem converges toward 1/e ≈ 0.368".

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem tendsto_optimalProb :
    Tendsto optimalProb atTop (𝓝 (Real.exp (-1))) := by sorry

end ClassicalSecretary
