-- Prove2me | Theorems.Thm_AlgMechDesign_MinWork_minwork_strongly_truthful
-- name    : AlgMechDesign.MinWork.minwork_strongly_truthful
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:17:55.907886+00:00
-- url     : https://prove2.me/theorems/b791b545-6153-4f27-8a52-42c0fb1c0819
-- title:
--   Claim 4.2 — MinWork is strongly truthful
-- statement:
--   Let $n \ge 2$ and $k \ge 0$, and let $x(\cdot)$ be any MinWork allocation rule, with the MinWork payments $p^i(d) = \sum_{j \in x^i(d)} \min_{i' \neq i} d^{i'}_j$. Then the mechanism $(x, p)$ is **strongly truthful** on positive types:
--
--   1. for every positive declaration profile $d^{-i}$ of the others, every positive true type $t^i$ and every positive misreport $d^i$,
--   $$
--   u^i\big(t^i \mid (d^i, d^{-i})\big) \le u^i\big(t^i \mid (t^i, d^{-i})\big), \qquad u^i(t^i \mid d) = p^i(d) - \sum_{j \in x^i(d)} t^i_j ;
--   $$
--   2. for every positive $t^i$ and every positive $d^i \neq t^i$ there is a positive $d^{-i}$ for which this inequality is strict.
--
--   That is, truth-telling is the only dominant strategy of each agent, for any number of tasks and any tie-breaking rule.
--
--   **Formalization Note** The paper writes its proof of the strict part for one task and two agents ("The argument for $k > 1$ is similar"); the statement here is for every $n \ge 2$ and every $k$. The printed proof also swaps the two utilities in the case $d^i > t^i$ (see the mission's description).
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 176, Claim 4.2 (proof p. 177)

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

namespace AlgMechDesign.MinWork

/-- Claim 4.2: for `n ≥ 2` agents, any number `k` of tasks and every tie-breaking rule, the
MinWork mechanism is strongly truthful on positive types. -/
theorem minwork_strongly_truthful {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsStronglyTruthful alloc (minWorkPay hn alloc) := by sorry

end AlgMechDesign.MinWork
