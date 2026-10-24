-- Prove2me | Theorems.Thm_BudgetClock_NonMonotone_corollary_1
-- name    : BudgetClock.NonMonotone.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:18.329641+00:00
-- url     : https://prove2.me/theorems/e70aa2c5-13fd-48eb-8eb1-21d801318124
-- title:
--   Corollary 1, p. 13 — the optimal bidders still active after phase t keep value at least OPT − 12·OP̃T_t
-- statement:
--   Let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a non-negative submodular valuation, let $c_i \ge 0$ be the bidders' costs and $B > 0$ the budget, and run Simultaneous-Iterative-Pruning (Mechanism 3). Let $O \subseteq N$ be any set with $\sum_{i \in O} c_i \le B$ (for instance an optimal one, with $v(O) = OPT$), and for a phase $t$ let $O^+_t$ be the set of bidders of $O$ that have not been rejected by the end of phase $t$. Then for every phase $1 \le t \le \hat t$,
--
--   $$v(O^+_t) \ge v(O) - 12\,\widetilde{OPT}_t,$$
--
--   where $\widetilde{OPT}_t = 2^{t-1}\max_i v(\{i\})$ is the target of phase $t$ and $\hat t$ is the last phase.
--
--   Because the targets double from phase to phase, the losses of Lemma 6 sum to at most twice the loss of the current phase. This corollary is what Lemma 7 combines with the unconstrained maximization step.
--
--   **Formalization Note**
--   1. The statement is for every budget-feasible $O$; for an optimal $O$ it is the paper's $v(O^+_t) \ge OPT - 12\widetilde{OPT}_t$.
--   2. No normalization $v(\emptyset) = 0$ is assumed (unlike in Lemma 6): the corollary holds without it.
--   3. $B > 0$ is added (the paper says only "a budget $B$").
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 13, Corollary 1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism

namespace BudgetClock.NonMonotone

/-- Corollary 1, p. 13: for every phase `1 ≤ t ≤ t̂` and every budget-feasible set `O` (stated for
all feasible `O`, in particular an optimal one, whose value is `OPT`), the bidders of `O` not
rejected by the end of phase `t` have value at least `v(O) - 12 OP̃T_t`. -/
theorem corollary_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (O : Finset (Fin n)) (hO : ∑ i ∈ O, c i ≤ B)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ lastPhase v c B) :
    v O - 12 * target v t ≤ v (O ∩ survivors v c B t) := by sorry

end BudgetClock.NonMonotone
