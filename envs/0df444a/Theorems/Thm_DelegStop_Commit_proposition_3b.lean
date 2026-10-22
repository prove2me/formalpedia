-- Prove2me | Theorems.Thm_DelegStop_Commit_proposition_3b
-- name    : DelegStop.Commit.proposition_3b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:10.297489+00:00
-- url     : https://prove2.me/theorems/1e11ed6e-e251-47f5-afbe-61bda47b975a
-- title:
--   Proposition 3 (b), p. 6323 (PDF 8) — under flexible stopping μ^{F+}_2 = μ_l, and (μ^F_1, μ^{F−}_2) switches at p̲ and p̄^F
-- statement:
--   Consider the two-round game of §3 under the standing assumptions of §3.2, with evaluation cost $c_I > 0$. Under the flexible stopping policy the provider chooses, by backward induction from (4)–(7), a second-round effort $\mu^{F+}_2$ after a feasible first solution, $\mu^{F-}_2$ after an infeasible one, and a first-round effort $\mu^F_1$ that anticipates the client's stopping rule.
--
--   **Proposition 3 (b).** For every payment $p > 0$, $\mu^{F+}_2 = \mu_l$. In addition, there exist thresholds $\underline p$ and $\bar p^F$ such that for every $p > 0$,
--   $$(\mu^F_1, \mu^{F-}_2) = \begin{cases} (\mu_l,\mu_l), & p < \underline p, \\ (\mu_l, \mu_h), & \underline p \le p < \bar p^F, \\ (\mu_h,\mu_h), & \bar p^F \le p. \end{cases}$$
--
--   Together with part (a), this shows how the flexible policy dampens the provider's incentive for high first-round effort.
--
--   **Formalization Note.** Only $T = 2$ is modelled. $\mu^{F+}_2$ is computed from (4) in the model, not fixed. The thresholds may depend on the model parameters and on $c_I$, but not on $p$. That the $\underline p$ here is the same as in part (a) follows from the uniqueness of such thresholds (both are determined by the effort map on $p > 0$); part (c) is stated for any thresholds satisfying (a) and (b).
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6323 (PDF 8), Proposition 3 (b)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem proposition_3b (P : Params) (hP : P.Standing) (cI : ℝ) (hcI : 0 < cI) :
    (∀ p : ℝ, 0 < p → effort2Fplus P p = Effort.low) ∧
    ∃ pLow pBarF : ℝ, FlexibleEffortThresholds P cI pLow pBarF := by sorry

end DelegStop.Commit
