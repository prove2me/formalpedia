-- Prove2me | Theorems.Thm_AlgMechDesign_CompBonus_cb_truthful
-- name    : AlgMechDesign.CompBonus.cb_truthful
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:19:35.771975+00:00
-- url     : https://prove2.me/theorems/561404f8-4f00-48af-8acf-15348bea0722
-- title:
--   Claim 5.2, proof — truth-telling with minimal execution is dominant
-- statement:
--   Let $x(\cdot)$ be an optimal allocation algorithm and consider the Compensation-and-Bonus mechanism based on it. Let $i$ be an agent with positive type $t^i$. Then the strategy
--
--   - declare $t^i$, and
--   - for every allocation $x$, perform each task $j \in x^i$ in its minimal time $t^i_j$
--
--   is dominant for agent $i$: whatever positive declarations and whatever execution plans the other agents use, no strategy consisting of a positive declaration and an execution plan feasible for $t^i$ gives agent $i$ a larger utility.
--
--   This is the truthfulness half of Claim 5.2; it is the conclusion of the first paragraph of its proof.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 188, proof of Claim 5.2, first paragraph

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Proof of Claim 5.2, first paragraph (p. 188): in the Compensation-and-Bonus mechanism based
on an optimal allocation algorithm, for every agent `i` of positive type `ti` the strategy
"declare `ti` and perform every allocated task `j` in its minimal time `tⁱ_j`" is dominant. -/
theorem cb_truthful {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc)
    (i : Fin n) (ti : Fin k → ℝ) (hti : IsAgentType ti) :
    Dominant alloc (cbPay alloc) i ti ti (fun _ j => ti j) := by sorry

end AlgMechDesign.CompBonus
