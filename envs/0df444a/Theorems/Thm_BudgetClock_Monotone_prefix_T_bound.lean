-- Prove2me | Theorems.Thm_BudgetClock_Monotone_prefix_T_bound
-- name    : BudgetClock.Monotone.prefix_T_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:25.602067+00:00
-- url     : https://prove2.me/theorems/75497ee5-c56c-4499-9de3-3e75824e3d69
-- title:
--   Appendix A.1, p. 20 — v(T) ≥ (u − 1/2^{t̂−2}) · OP̃T_t̂ / 2
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation, $c_i \ge 0$ the costs and $B > 0$ the budget, and run Iterative-Pruning, with final prices $p$. Assume $\overline W_2$ is budget feasible, so that $W_2 = \overline W_2$, and let
--   $$u = 1 - \frac{\sum_{i \in W_2} p_i}{B}$$
--   be the fraction of the budget left unused by $W_2$. Then the prefix $T$ of $W_1$ chosen by Maximize-Value (the longest prefix with $W_2 \cup T$ budget feasible) satisfies
--   $$v(T) \ge \Bigl(u - \frac1{2^{\hat t-2}}\Bigr)\,\widetilde{\mathrm{OPT}}_{\hat t-1} = \Bigl(u - \frac1{2^{\hat t-2}}\Bigr)\frac{\widetilde{\mathrm{OPT}}_{\hat t}}{2}.$$
--
--   This lower bound on the value of $T$ feeds the upper constraint (15) on $v(W_1 \cup W_2)/\widetilde{\mathrm{OPT}}_{\hat t}$ in the proof of Theorem 1.
--
--   **Formalization Note** The bound is stated in its final form, with $\widetilde{\mathrm{OPT}}_{\hat t}/2$. The case in which all of $W_1$ fits in the leftover budget (no prefix $T'$ exceeds $uB$) is included; there $T = W_1$. $B > 0$ is added.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 20, Appendix A.1, proof of Theorem 1 (bound on v(T) before (15))

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Appendix A.1, p. 20: if `t̂ ≥ 3` and `W̄_2` is budget feasible (`W_2 = W̄_2`), then with
`u = 1 − (∑_{i ∈ W_2} p_i)/B` the prefix `T` of Algorithm 2 has
`v(T) ≥ (u − 1/2^{t̂−2}) · OP̃T_t̂ / 2`. -/
theorem prefix_T_bound {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (h3 : 3 ≤ lastPhase v c B) (hW2 : W2 v c B = W2bar v c B) :
    (1 - listCost (finalPrices v c B) (W2 v c B) / B - 1 / (2 : ℝ) ^ (lastPhase v c B - 2)) *
        target v c B (lastPhase v c B) / 2 ≤
      v (Tpre v c B).toFinset := by sorry

end BudgetClock.Monotone
