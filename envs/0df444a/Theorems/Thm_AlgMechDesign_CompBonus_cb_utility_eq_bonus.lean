-- Prove2me | Theorems.Thm_AlgMechDesign_CompBonus_cb_utility_eq_bonus
-- name    : AlgMechDesign.CompBonus.cb_utility_eq_bonus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:01:02.330923+00:00
-- url     : https://prove2.me/theorems/ea6152f4-7579-4ec5-9722-a8b6c3571614
-- title:
--   Claim 5.2, proof — the utility of an agent equals its bonus
-- statement:
--   Consider the Compensation-and-Bonus payments $p^i = c^i + b^i$ built on an arbitrary allocation rule $x(\cdot)$. Let $d$ be any declaration profile and let every agent follow any execution plan, producing actual times $\tilde t$. Then the utility of every agent $i$ equals its bonus:
--   $$
--   p^i(d,\tilde t) - \sum_{j \in x^i(d)} \tilde t_j \;=\; b^i(d, \tilde t) \;=\; -g\big(x(d), \mathrm{corr}^i(x(d), d, \tilde t)\big).
--   $$
--
--   The compensation exactly reimburses the agent's actual work, so its incentives are driven by the bonus alone. This is the first observation of the proof of Claim 5.2.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 188, proof of Claim 5.2, first paragraph, third sentence ("Observing that the utility of an agent equals its bonus, …")

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

namespace AlgMechDesign.CompBonus

/-- Proof of Claim 5.2 (p. 188): in the Compensation-and-Bonus mechanism based on any allocation
algorithm, the utility of agent `i` (payment plus valuation) equals its bonus, for all
declarations `d` and all execution plans `E`. -/
theorem cb_utility_eq_bonus {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (d : Fin n → Fin k → ℝ)
    (E : Fin n → ExecPlan n k) (i : Fin n) :
    utility alloc (cbPay alloc) d E i = bonus alloc d (actualTimes alloc d E) i := by sorry

end AlgMechDesign.CompBonus
