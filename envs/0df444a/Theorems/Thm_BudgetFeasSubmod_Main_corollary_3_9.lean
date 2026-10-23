-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_corollary_3_9
-- name    : BudgetFeasSubmod.Main.corollary_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:04.914163+00:00
-- url     : https://prove2.me/theorems/32da53b3-2c07-4084-aa71-250632be72f5
-- title:
--   Corollary 3.9, p. 13 — the set S returned by GenSm-Main satisfies 505 · E(v(S)) ≥ opt(A, B)
-- statement:
--   Let $A$ be a nonempty finite set of agents, $v$ a normalized non-negative submodular valuation, $B>0$ and $c\in[0,B]^A$ the costs. Let $\mathrm{alg}_1$ be a deterministic e-approximation for the knapsack-constrained problem, $\mathrm{alg}_2$ a 2-approximation for unconstrained maximization, and fix a cost-independent arg-max tie-breaking rule. Then the set $S$ returned by GenSm-Main$(A,v,c,B)$ (with $p=0.201$, $\beta=9.185$) satisfies
--   $$
--   505\cdot\mathbb E(v(S))\ge\mathrm{opt}(A,B).
--   $$
--
--   This is the approximation half of Theorem 3.1, with the explicit constant $505$.
--
--   **Formalization Note** $\mathbb E(v(S))=p\,v(\{i^*\})+\frac{1-p}{2^{|A|}}\sum_{A_1\subseteq A}v(S_{A_1})$, where $S_{A_1}$ is the output of Sample-then-Greedy with first half $A_1$. $\mathrm{alg}_1$ is deterministic (footnote 3, Remark 3.10); the paper notes that a randomized $\mathrm{alg}_1$ gives $505+\varepsilon$.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 13, Corollary 3.9

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

open Finset

/-- Corollary 3.9, p. 13: the set `S` returned by GenSm-Main(A, v, c, B) satisfies
`505 · E(v(S)) ≥ opt(A, B)`. -/
theorem corollary_3_9 {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ) (c : A → ℝ)
    (hv : IsValuation v) (h1 : IsKnapsackEApprox v B alg1) (h2 : IsUnconstrainedTwoApprox v alg2)
    (htb : IsArgmaxRule v tb) (hB : 0 < B) (hc : InDomain B c) :
    opt v c B univ ≤ 505 * expectedValue v alg1 alg2 tb B c := by sorry

end BudgetFeasSubmod.Main
