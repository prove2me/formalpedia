-- Prove2me | Theorems.Thm_AlgMechDesign_CompBonus_cb_strongly_truthful
-- name    : AlgMechDesign.CompBonus.cb_strongly_truthful
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T21:24:25.33607+00:00
-- url     : https://prove2.me/theorems/6438cb41-8805-448c-8f93-383cfddead77
-- title:
--   Claim 5.2 — the Compensation-and-Bonus mechanism is strongly truthful
-- statement:
--   Let there be $n \ge 2$ agents and any number $k$ of tasks, and let $x(\cdot)$ be any optimal allocation algorithm (ties broken arbitrarily). Then the Compensation-and-Bonus mechanism based on $x(\cdot)$ is **strongly truthful**:
--
--   1. for every agent $i$ and every positive type $t^i$, declaring $t^i$ and performing each allocated task in minimal time is a dominant strategy, and
--   2. every dominant strategy of agent $i$ declares exactly $t^i$ and performs every task it may be allocated, under every allocation, in exactly its minimal time $t^i_j$.
--
--   Strong truthfulness is what makes the mechanism's outcome predictable: rational agents have exactly one way to play.
--
--   **Formalization Note** The hypothesis $n \ge 2$ is not printed with the claim. With a single agent the allocation does not depend on the declaration, so every positive declaration is dominant and part 2 fails as soon as $k \ge 1$. Declarations range over positive vectors, the type space of Definition 10.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 188, Claim 5.2 and its proof

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Claim 5.2 (p. 188): for `n ≥ 2` agents and every optimal allocation algorithm (ties broken
arbitrarily), the Compensation-and-Bonus mechanism is strongly truthful: truth-telling with
minimal execution is dominant, and it is the only dominant strategy. -/
theorem cb_strongly_truthful {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) := by sorry

end AlgMechDesign.CompBonus
