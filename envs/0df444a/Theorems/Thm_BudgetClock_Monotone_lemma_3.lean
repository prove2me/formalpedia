-- Prove2me | Theorems.Thm_BudgetClock_Monotone_lemma_3
-- name    : BudgetClock.Monotone.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:18.263518+00:00
-- url     : https://prove2.me/theorems/3b761fec-77ce-4896-ad62-f3f1609dbdbb
-- title:
--   Lemma 3, p. 9 — if S_t is not budget feasible, v(S_t ∖ {i_t}) ≥ 2^{t−1}/(2^{t−1}+1) · OP̃T_t
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation, $c_i \ge 0$ the costs and $B > 0$ the budget, and run Iterative-Pruning. Let $2 \le t \le \hat t$ be a phase, $S_t$ the set built in phase $t$, $i_t$ the last bidder added to it, and $\widetilde{\mathrm{OPT}}_t$ the target of the phase. If $S_t$ is not budget feasible at the prices at the end of phase $t$, i.e. $\sum_{i\in S_t} p_i > B$, then
--   $$v(S_t \setminus \{i_t\}) \ge \frac{2^{t-1}}{2^{t-1}+1}\cdot \widetilde{\mathrm{OPT}}_t.$$
--
--   The lemma bounds the value lost when the last bidder of a set is discarded to restore budget feasibility.
--
--   **Formalization Note** $S_t \setminus \{i_t\}$ is the list $S_t$ without its last entry. The paper's "for all $t \ge 2$" is read as the phases $2 \le t \le \hat t$ that the mechanism runs. The paper's hypothesis is submodularity only; the section's standing assumptions (monotonicity, $v \ge 0$, $c \ge 0$) are kept, and $B > 0$ is added.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 9, Lemma 3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Lemma 3, p. 9: for a phase `2 ≤ t ≤ t̂` whose set `S_t` is not budget feasible at the prices at the end
of phase `t`, removing the last bidder `i_t` added to `S_t` leaves
`v(S_t \ {i_t}) ≥ 2^{t−1}/(2^{t−1}+1) · OP̃T_t`. -/
theorem lemma_3 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (t : ℕ) (ht2 : 2 ≤ t) (htle : t ≤ lastPhase v c B)
    (hinf : B < listCost (phasePrices v c B t) (phaseSet v c B t)) :
    ((2 : ℝ) ^ (t - 1) / ((2 : ℝ) ^ (t - 1) + 1)) * target v c B t ≤
      v (phaseSet v c B t).dropLast.toFinset := by sorry

end BudgetClock.Monotone
