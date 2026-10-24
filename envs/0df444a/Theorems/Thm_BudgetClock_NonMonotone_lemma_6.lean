-- Prove2me | Theorems.Thm_BudgetClock_NonMonotone_lemma_6
-- name    : BudgetClock.NonMonotone.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:16.965833+00:00
-- url     : https://prove2.me/theorems/a67a3817-6f7d-4e2d-8047-d42c22dddfc2
-- title:
--   Lemma 6, p. 12 — the optimal bidders rejected in phase t have value at most 6·OP̃T_t
-- statement:
--   Let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a non-negative submodular valuation on $n$ bidders, with $n \ge 2$ or $v(\emptyset) = 0$, let $c_i \ge 0$ be the bidders' costs and $B > 0$ the budget, and run Simultaneous-Iterative-Pruning (Mechanism 3). Let $O \subseteq N$ be any set with $\sum_{i \in O} c_i \le B$ (for instance an optimal one), and for a phase $t$ let $O^-_t$ be the set of bidders of $O$ rejected in phase $t$. Then for every phase $1 \le t \le \hat t$,
--
--   $$v(O^-_t) \le 6\,\widetilde{OPT}_t,$$
--
--   where $\widetilde{OPT}_t = 2^{t-1}\max_i v(\{i\})$ is the target of phase $t$ and $\hat t$ is the last phase.
--
--   This bounds the value lost to the rejections of a single phase. Summed over the phases it gives Corollary 1, and from there the 64-approximation of Theorem 5.
--
--   **Formalization Note**
--   1. The page prints "$v(O^-_t) \ge 6\widetilde{OPT}_t$". That is a typo: the proof ends with "$v(O^-_t) \le 6\widetilde{OPT}_t$ for all $t$", Corollary 1 uses the upper bound, and the lower bound is false whenever $O^-_t = \emptyset$ and $v$ is not identically zero. The upper bound is stated.
--   2. The statement is for every budget-feasible $O$, which is stronger than for an optimal one; the proof uses only $\sum_{i \in O} c_i \le B$.
--   3. The hypothesis "$n \ge 2$ or $v(\emptyset) = 0$" is added; the paper never assumes a normalization. Without it the lemma fails: for $n = 1$, $v(\emptyset) = 1$, $v(\{0\}) = 0$, no phase after phase 1 runs, $O^-_1 = \emptyset$ and $\widetilde{OPT}_1 = 0$. For $n \ge 2$ the lemma holds for every non-negative submodular $v$, so only this one-bidder corner is excluded.
--   4. $B > 0$ is added (the paper says only "a budget $B$"); the prices divide by quantities proportional to $B$.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 12, Lemma 6 (proof on pp. 12–13)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism

namespace BudgetClock.NonMonotone

/-- Lemma 6, p. 12: for every phase `1 ≤ t ≤ t̂` and every budget-feasible set `O` (stated for
all feasible `O`, in particular an optimal one), the bidders of `O` rejected in phase `t` have
value at most `6 OP̃T_t`. The page prints `v(O⁻_t) ≥ 6OP̃T_t`; its proof ends with
`v(O⁻_t) ≤ 6OP̃T_t` and Corollary 1 uses `≤`, so `≤` is stated. `2 ≤ n ∨ v ∅ = 0` is added:
without it the lemma fails for `n = 1`, `v ∅ = 1`, `v {0} = 0` (then `t̂ = 1`, `O⁻_1 = ∅`,
`OP̃T_1 = 0`); for `n ≥ 2` no normalization is needed. -/
theorem lemma_6 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (hn : 2 ≤ n ∨ v ∅ = 0)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (O : Finset (Fin n)) (hO : ∑ i ∈ O, c i ≤ B)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ lastPhase v c B) :
    v (O ∩ rejectedIn v c B t) ≤ 6 * target v t := by sorry

end BudgetClock.NonMonotone
