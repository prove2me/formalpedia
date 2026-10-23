-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_theorem_3_1
-- name    : BudgetFeasSubmod.Main.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:30.605985+00:00
-- url     : https://prove2.me/theorems/40ae699a-b73b-4758-bafb-ec9a7f8d9090
-- title:
--   Theorem 3.1, p. 7 (with Corollary 3.9, p. 13) — GenSm-Main is universally truthful, individually rational, budget-feasible and 505 · E(v(S)) ≥ opt(A, B)
-- statement:
--   Let $A$ be a nonempty finite set of agents with private costs, $v$ a normalized non-negative submodular valuation (not necessarily monotone) and $B>0$ a budget. Let $\mathrm{alg}_1$ be a deterministic, cost-local e-approximation for maximizing $v$ under the knapsack constraint, $\mathrm{alg}_2$ a 2-approximation for unconstrained maximization of $v$, and fix a tie-breaking rule that does not depend on the declared costs. Consider the randomized mechanism GenSm-Main: with probability $p=0.201$ it selects a single agent $i^*$ of largest value $v(i^*)$; otherwise it splits $A$ uniformly at random into $A_1,A_2$, sets $x=v(\mathrm{alg}_1(A_1))$ and runs Simultaneous Greedy on $A_2$ with rate $x$ and $\beta=9.185$; winners receive Myerson's threshold payments. Then:
--
--   1. GenSm-Main is **universally truthful, individually rational and budget-feasible**: each deterministic mechanism in its support is truthful, individually rational, and pays at most $B$ in total, for all declarations in $[0,B]^A$;
--   2. it is a **505-approximation**: for every cost vector $c\in[0,B]^A$, the returned set $S$ satisfies
--   $$
--   505\cdot\mathbb E(v(S))\ge\mathrm{opt}(A,B).
--   $$
--
--   This is the main result of the paper's offline part: the first constant-factor budget-feasible mechanism for non-monotone submodular objectives, Theorem 3.1's "$O(1)$" made explicit by Corollary 3.9.
--
--   **Formalization Note** The randomness is the explicit finite family $\{\text{singleton}\}\cup\{A_1\subseteq A\}$ with weights $p$ and $(1-p)/2^{|A|}$, and $\mathbb E$ is the weighted sum. Bids and misreports lie in $[0,B]$ (Remark 2.5). $\mathrm{alg}_1$ is assumed deterministic (footnote 3, Remark 3.10) and cost-local (it is run on $(A_1,v,c_{A_1},B)$); $\mathrm{alg}_2$ sees only its input set; tie-breaking sees only $(U,S_1,S_2)$ (Remark 2.6). The polynomial running time is not formalized.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 7, Theorem 3.1, and p. 13, Corollary 3.9

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

open Finset

/-- Theorem 3.1, p. 7, with the constant of Corollary 3.9, p. 13: GenSm-Main is universally
truthful, individually rational and budget-feasible (every deterministic mechanism in its support,
with threshold payments, has the three properties), and `505 · E(v(S)) ≥ opt(A, B)`. -/
theorem theorem_3_1 {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ)
    (hv : IsValuation v) (hB : 0 < B)
    (h1 : IsKnapsackEApprox v B alg1) (h1loc : IsCostLocal alg1)
    (h2 : IsUnconstrainedTwoApprox v alg2) (htb : IsArgmaxRule v tb) :
    (∀ ω : Option (Finset A),
      IsTruthful (genSmMain v alg1 alg2 tb B ω) B ∧
        IsIR (genSmMain v alg1 alg2 tb B ω) B ∧
        IsBudgetFeasible (genSmMain v alg1 alg2 tb B ω) B) ∧
    (∀ c : A → ℝ, InDomain B c → opt v c B univ ≤ 505 * expectedValue v alg1 alg2 tb B c) := by sorry

end BudgetFeasSubmod.Main
