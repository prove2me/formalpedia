-- Prove2me | Theorems.Thm_AlgMechDesign_CompBonus_comp_bonus_strongly_truthful
-- name    : AlgMechDesign.CompBonus.comp_bonus_strongly_truthful
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:28:39.471704+00:00
-- url     : https://prove2.me/theorems/edd1db20-c8a1-4e44-afd2-1633e961d709
-- title:
--   Theorem 5.1 — Compensation-and-Bonus is a strongly truthful implementation of task scheduling
-- statement:
--   Consider task scheduling with verification: $n \ge 2$ agents, $k$ tasks, agent $i$ needs at least $t^i_j > 0$ time units for task $j$, the mechanism chooses the allocation from the declared types and pays each agent after observing the actual times in which the tasks were performed. Let $x(\cdot)$ be any optimal allocation algorithm (ties broken arbitrarily) and let the payments be the Compensation-and-Bonus payments
--   $$
--   p^i(d,\tilde t) = \sum_{j \in x^i(d)} \tilde t_j \;-\; g\big(x(d), \mathrm{corr}^i(x(d), d, \tilde t)\big).
--   $$
--   Then this mechanism is a **strongly truthful implementation** of the task scheduling problem:
--
--   1. it is strongly truthful: for each agent the only dominant strategy is to declare its true type and to perform each of its tasks in minimal time; and
--   2. whenever every agent plays a dominant strategy for its true type $t^i$, the resulting allocation $x$ and actual times $\tilde t$ attain the optimal make-span,
--   $$
--   g(x, \tilde t) \le g(y, t) \quad \text{for every allocation } y .
--   $$
--
--   With verification of the actual execution times, the make-span of unrelated machines can therefore be minimized exactly by a truthful mechanism, whereas without verification no mechanism achieves an approximation ratio below 2 (Theorem 4.6 of the same paper).
--
--   **Formalization Note** The hypothesis $n \ge 2$ is not printed with the theorem; it is needed for the uniqueness of the dominant strategy (with one agent every positive declaration is dominant). "Implementation" is Definition 3's requirement that every tuple of dominant strategies yields an output meeting the specification, here the exact optimum; part 2 is stated for every profile of dominant strategies, not only the truthful one. Running time is not modelled.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 188, Theorem 5.1 (with Definition 3, p. 172, second bullet)

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Theorem 5.1 (p. 188): for `n ≥ 2` agents and every optimal allocation algorithm (ties broken
arbitrarily), the Compensation-and-Bonus mechanism is a strongly truthful implementation of the
task scheduling problem: it is strongly truthful, and whenever every agent plays a dominant
strategy for its true type the output attains the optimal make-span. -/
theorem comp_bonus_strongly_truthful {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) ∧ ImplementsOptimum alloc (cbPay alloc) := by sorry

end AlgMechDesign.CompBonus
