-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_4
-- name    : BudgetFeasSubmod.Main.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:57.491226+00:00
-- url     : https://prove2.me/theorems/b3af70b8-16e3-4ec7-bdef-06ff8e2c4d66
-- title:
--   Lemma 3.4, p. 9 — Simultaneous Greedy with threshold payments is budget-feasible
-- statement:
--   Let $v$ be a normalized non-negative submodular valuation on a finite agent set $A$, $B>0$, $\beta>0$, $x\in\mathbb R$ and $D\subseteq A$. Fix a cost-independent arg-max tie-breaking rule and a subroutine $\mathrm{alg}_2$ that returns a subset of its input. Then for every declaration $b\in[0,B]^A$ the threshold payments of the outcome rule Simultaneous Greedy$(D,v,b_D,B,x)$ satisfy
--   $$
--   \sum_{i\in A}p_i(b)\le B.
--   $$
--
--   Together with Lemma 3.3 this makes Simultaneous Greedy a truthful, individually rational, budget-feasible mechanism for every fixed rate $x$.
--
--   **Formalization Note** The payments are the threshold payments computed from the outcome rule, not the posted prices; $\mathrm{alg}_2$ enters through the 2-approximation specification, of which only $T_j\subseteq S_j$ is relevant here. $\beta>0$ and $x$ are arbitrary, as in Lemma 3.3.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 9, Lemma 3.4

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

/-- Lemma 3.4, p. 9: Simultaneous Greedy with threshold payments is budget-feasible. -/
theorem lemma_3_4 {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ)
    (alg2 : Finset A → Finset A) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (D : Finset A)
    (hv : IsValuation v) (h2 : IsUnconstrainedTwoApprox v alg2) (htb : IsArgmaxRule v tb)
    (hβ : 0 < β) (hB : 0 < B) :
    IsBudgetFeasible (simGreedy v alg2 tb β B x D) B := by sorry

end BudgetFeasSubmod.Main
