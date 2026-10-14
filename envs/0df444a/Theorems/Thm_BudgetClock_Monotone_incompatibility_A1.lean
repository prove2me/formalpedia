-- Prove2me | Theorems.Thm_BudgetClock_Monotone_incompatibility_A1
-- name    : BudgetClock.Monotone.incompatibility_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:20.664397+00:00
-- url     : https://prove2.me/theorems/66077af0-d448-49a7-9781-e6fd5bc682c3
-- title:
--   Appendix A.1, pp. 20–21 — the three constraints on v(W₁ ∪ W₂)/OP̃T_t̂ are incompatible for ρ ≥ 4.75
-- statement:
--   Let $t \ge 3$ be an integer and $\rho, \alpha, \beta, u$ real numbers with
--   $$\rho \ge 4.75, \qquad \alpha \ge \frac{2^{t-2}}{2^{t-1}+2}, \qquad \beta \le \frac32 - \frac1{2^{t-2}}, \qquad 0 \le u \le 1.$$
--   Then there is no real number $x$ with
--   $$x > \rho\alpha - \beta, \qquad x > \rho(1-u) - \beta, \qquad x < \frac{2\rho\alpha + 2\beta - \rho u + \frac{\rho}{2^{t-2}}}{2\rho-2}.$$
--
--   In the proof of Theorem 1, $t = \hat t$, $x = v(W_1 \cup W_2)/\widetilde{\mathrm{OPT}}_{\hat t}$, $\alpha = v(W_1)/\widetilde{\mathrm{OPT}}_{\hat t}$, $\beta = v(R \mid W_1 \cup W_2)/\widetilde{\mathrm{OPT}}_{\hat t}$, and the three inequalities are what follows from assuming that both $v(W_1)$ and $v(W_3)$ are below a $1/\rho$ fraction of the benchmark. Their incompatibility yields the factor $4.75$.
--
--   **Formalization Note** The bound on $\beta$ uses Lemma 2's constant $1/2^{t-2}$; the appendix quotes $1/2^{t-1}$ once but substitutes $1/2^{t-2}$ in the computation that follows. All three inequalities are strict, as printed; at $t = 3$, $\rho = 4.75$, $u = 1 - \alpha$ and the extreme $\alpha, \beta$ the lower and upper bounds coincide.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, pp. 20–21, Appendix A.1, proof of Theorem 1 (the three constraints and their incompatibility)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Appendix A.1, pp. 20–21: for `t ≥ 3`, `ρ ≥ 4.75`, `α ≥ 2^{t−2}/(2^{t−1}+2)`,
`β ≤ 3/2 − 1/2^{t−2}` and `0 ≤ u ≤ 1`, no real `x` (the ratio `v(W_1 ∪ W_2)/OP̃T_t̂`) satisfies the three
constraints `x > ρα − β`, `x > ρ(1 − u) − β`, `x < (2ρα + 2β − ρu + ρ/2^{t−2})/(2ρ − 2)`. -/
theorem incompatibility_A1 (t : ℕ) (ht : 3 ≤ t) (ρ α β u x : ℝ) (hρ : 19 / 4 ≤ ρ)
    (hα : (2 : ℝ) ^ (t - 2) / ((2 : ℝ) ^ (t - 1) + 2) ≤ α)
    (hβ : β ≤ 3 / 2 - 1 / (2 : ℝ) ^ (t - 2)) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ¬ (ρ * α - β < x ∧ ρ * (1 - u) - β < x ∧
        x < (2 * ρ * α + 2 * β - ρ * u + ρ / (2 : ℝ) ^ (t - 2)) / (2 * ρ - 2)) := by sorry

end BudgetClock.Monotone
