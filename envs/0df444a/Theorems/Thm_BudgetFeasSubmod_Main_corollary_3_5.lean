-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_corollary_3_5
-- name    : BudgetFeasSubmod.Main.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:07.081633+00:00
-- url     : https://prove2.me/theorems/b7a2ee61-f65b-4709-b5c5-fc6c53d0fa1e
-- title:
--   Corollary 3.5, p. 10 — GenSm-Main is universally truthful, individually rational and budget-feasible
-- statement:
--   Let $A$ be a nonempty finite set of agents, $v$ a normalized non-negative submodular valuation, $B>0$. Let $\mathrm{alg}_1$ be a deterministic cost-local subroutine, $\mathrm{alg}_2$ a subroutine returning subsets of its input with $\mathrm{opt}(S,\infty)\le 2v(\mathrm{alg}_2(S))$, and fix a cost-independent arg-max tie-breaking rule. Then every deterministic mechanism in the support of GenSm-Main — the singleton mechanism returning $\{i^*\}$, and for each $A_1\subseteq A$ the mechanism Simultaneous Greedy$(A\setminus A_1,v,c_{A\setminus A_1},B,v(\mathrm{alg}_1(A_1)))$ with $\beta=9.185$ — is, with threshold payments, truthful, individually rational and budget-feasible.
--
--   Since GenSm-Main is a probability distribution over these mechanisms (weights $p=0.201$ and $(1-p)/2^{|A|}$), it is universally truthful, individually rational and budget-feasible: the first half of Theorem 3.1.
--
--   **Formalization Note** Universal truthfulness is stated as truthfulness of every member of the explicit finite family `genSmMain … ω`, $\omega\in\{\text{none}\}\cup\{A_1\subseteq A\}$. Cost-locality of $\mathrm{alg}_1$ (it reads only $c_{A_1}$, as in "$\mathrm{alg}_1(A_1,v,c_{A_1},B)$") and its determinism (footnote 3, Remark 3.10) are hypotheses. The polynomial running time asserted in the proof is not formalized.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 10, Corollary 3.5

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

/-- Corollary 3.5, p. 10: every deterministic mechanism in the support of GenSm-Main, with
threshold payments, is truthful, individually rational and budget-feasible. -/
theorem corollary_3_5 {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ)
    (hv : IsValuation v) (h1 : IsCostLocal alg1) (h2 : IsUnconstrainedTwoApprox v alg2)
    (htb : IsArgmaxRule v tb) (hB : 0 < B) :
    ∀ ω : Option (Finset A),
      IsTruthful (genSmMain v alg1 alg2 tb B ω) B ∧
        IsIR (genSmMain v alg1 alg2 tb B ω) B ∧
        IsBudgetFeasible (genSmMain v alg1 alg2 tb B ω) B := by sorry

end BudgetFeasSubmod.Main
