-- Prove2me | Theorems.Thm_ClassicalSecretary_successProb_cutoffRule
-- name    : ClassicalSecretary.successProb_cutoffRule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:50:44.115204+00:00
-- url     : https://prove2.me/theorems/6cb8d240-797f-41e9-80b4-95c31dca12f8
-- title:
--   Success probability of the cutoff rule: $P(r)=\frac{r-1}{n}\sum_{i=r}^n\frac1{i-1}$
-- statement:
--   Let $2 \le r \le n$. The cutoff rule that rejects the first $r-1$ applicants and then accepts the first applicant who is better than all earlier ones selects the best applicant with probability
--   $$P_n(\text{cutoff } r) = \frac{r-1}{n}\sum_{i=r}^{n}\frac{1}{i-1}.$$
--
--   This exact formula is the basis for both the small-$n$ table and the asymptotic analysis of the optimal cutoff.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy", displayed formula for P(r).

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem successProb_cutoffRule (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    successProb n (cutoffRule r) =
      ((r : ℝ) - 1) / (n : ℝ) * ∑ i ∈ Icc r n, 1 / ((i : ℝ) - 1) := by sorry

end ClassicalSecretary
