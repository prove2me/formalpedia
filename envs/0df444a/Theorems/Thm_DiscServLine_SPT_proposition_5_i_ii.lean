-- Prove2me | Theorems.Thm_DiscServLine_SPT_proposition_5_i_ii
-- name    : DiscServLine.SPT.proposition_5_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:36.743669+00:00
-- url     : https://prove2.me/theorems/e6fd9cde-7326-49a7-a3c4-d75829af13f8
-- title:
--   Proposition 5 (i)–(ii), p. 18 (PDF 18) — the optimal SPT line has variety (t̲ < t̄) and no cutoff (Λ₀ = Λ)
-- statement:
--   Assume $0<c<\bar\theta$, $b>0$ and $\Lambda>0$, with homogeneous customers ($\Delta=0$) and non-preemptive SPT. Then problem (9) has an optimal service line, and every optimal service line $(\underline t,\bar t,\mu)$ satisfies
--
--   1. **service variety:** $\underline t<\bar t$;
--   2. **no customer cutoff:** $\Lambda_0=\Lambda$.
--
--   Part (i) says that even with identical customers the firm offers several service durations under SPT, in contrast with FIFO, where the line collapses to a single service. Since a single service is a feasible design here, (i) is a genuine optimality statement.
--
--   **Formalization Note** Existence of an optimum, presupposed by "the optimal service line design", is stated explicitly.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 18 (PDF 18), Proposition 5 (i)–(ii)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem proposition_5_i_ii (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧ ∀ d, IsOptimal P d → d.lo < d.hi ∧ d.Λk 0 = P.Λ := by sorry

end DiscServLine.SPT
