-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_3
-- name    : BudgetFeasSubmod.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:13.577989+00:00
-- url     : https://prove2.me/theorems/37d57f83-f996-48a7-9809-8833eceb8b5e
-- title:
--   Lemma 3.3, p. 9 — Simultaneous Greedy is monotone, hence truthful and individually rational with threshold payments
-- statement:
--   Let $v$ be a normalized non-negative submodular valuation on a finite agent set $A$, $B>0$, $\beta>0$, $x\in\mathbb R$ and $D\subseteq A$. Fix a cost-independent arg-max tie-breaking rule and any $\mathrm{alg}_2$ (a function of the set alone). Then the outcome rule $b\mapsto$ Simultaneous Greedy$(D,v,b_D,B,x)$ is monotone on $[0,B]^A$, and with Myerson's threshold payments the resulting mechanism is truthful and individually rational.
--
--   Monotonicity is what makes the posted-price greedy usable as a mechanism: it is the hypothesis of Lemma 2.4 and the first half of the universal truthfulness of GenSm-Main.
--
--   **Formalization Note** The parameter $\beta$ is any positive real (the paper's analysis is independent of its value; GenSm-Main uses $\beta=9.185$), and $x$ is any real, including $x\le0$, since the lemma is applied with $x=v(\mathrm{alg}_1(A_1))$ for every $A_1$. Bids and misreports lie in $[0,B]$ (Remark 2.5).
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 9, Lemma 3.3

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

/-- Lemma 3.3, p. 9: the allocation rule of Simultaneous Greedy is monotone, and with threshold
payments it is truthful and individually rational. -/
theorem lemma_3_3 {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ)
    (alg2 : Finset A → Finset A) (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2)
    (β B x : ℝ) (D : Finset A)
    (hv : IsValuation v) (htb : IsArgmaxRule v tb) (hβ : 0 < β) (hB : 0 < B) :
    IsMonotoneRule (simGreedy v alg2 tb β B x D) B ∧
      IsTruthful (simGreedy v alg2 tb β B x D) B ∧
      IsIR (simGreedy v alg2 tb β B x D) B := by sorry

end BudgetFeasSubmod.Main
