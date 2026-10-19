-- Prove2me | Theorems.Thm_DelegStop_Commit_proposition_3a
-- name    : DelegStop.Commit.proposition_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:16.983488+00:00
-- url     : https://prove2.me/theorems/d86e1580-ab9f-43bb-b928-52d83a888018
-- title:
--   Proposition 3 (a), p. 6323 (PDF 8) — the provider's efforts (μ^C_1, μ^C_2) under committed stopping switch at p̲ and p̄^C
-- statement:
--   Consider the two-round game of §3 under the standing assumptions of §3.2. Under the committed stopping policy the provider chooses, by backward induction from (9)–(10), a second-round effort $\mu^C_2$ and then a first-round effort $\mu^C_1$, each in $\{\mu_l,\mu_h\}$, as functions of the payment $p$.
--
--   **Proposition 3 (a).** There exist thresholds $\underline p$ and $\bar p^C$ such that for every payment $p > 0$,
--   $$(\mu^C_1, \mu^C_2) = \begin{cases} (\mu_l,\mu_l), & p < \underline p, \\ (\mu_l, \mu_h), & \underline p \le p < \bar p^C, \\ (\mu_h,\mu_h), & \bar p^C \le p. \end{cases}$$
--
--   The middle case is the escalation of effort over the rounds that the paper highlights: the provider may hold back in round 1 because it can raise its effort in round 2.
--
--   **Formalization Note.** Only $T = 2$ is modelled. The thresholds depend on the model parameters $(\mu_l,\mu_h,c_l,c_h,k)$ and not on $p$: they are chosen before $p$ is quantified. The committed efforts do not depend on $c_I$. The provider takes high effort when indifferent, which gives the closed intervals of the page.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6323 (PDF 8), Proposition 3 (a)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem proposition_3a (P : Params) (hP : P.Standing) :
    ∃ pLow pBarC : ℝ, CommittedEffortThresholds P pLow pBarC := by sorry

end DelegStop.Commit
