-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_definition_2_1
-- name    : BudgetFeasSubmod.Main.definition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:01.401405+00:00
-- url     : https://prove2.me/theorems/9e12f806-3421-4d3b-b978-0363bd8d6d55
-- title:
--   Definition 2.1, pp. 5–6 — the three definitions of submodularity are equivalent
-- statement:
--   Let $A$ be a finite set and $v:2^A\to\mathbb R$ any set function, with marginal values $v(i\mid S)=v(S\cup\{i\})-v(S)$. Then the following are equivalent:
--
--   1. (ii) $v(S)+v(T)\ge v(S\cup T)+v(S\cap T)$ for all $S,T\subseteq A$;
--   2. (i) $v(i\mid S)\ge v(i\mid T)$ for all $S\subseteq T\subseteq A$ and $i\notin T$;
--   3. (iii) for all $S,T\subseteq A$,
--   $$
--   v(T)\le v(S)+\sum_{i\in T\setminus S}v(i\mid S)-\sum_{i\in S\setminus T}v\big(i\mid (S\cup T)\setminus\{i\}\big).
--   $$
--
--   Form (i) is the usual diminishing-returns definition; form (iii) is the one the analysis of Simultaneous Greedy uses to bound the value of an optimal solution in terms of marginal values.
--
--   **Formalization Note** The statement is two equivalences, (ii) ⇔ (i) and (ii) ⇔ (iii), with (ii) the published lattice definition `Submodular`. No normalization, sign or monotonicity of $v$ is assumed, as on the page.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, pp. 5–6, Definition 2.1

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

open Finset NonmonotoneSubmod.Shared

/-- Definition 2.1, pp. 5–6: for a set function on a finite ground set, the lattice form (ii) of
submodularity is equivalent to the decreasing-marginals form (i) and to the form (iii). -/
theorem definition_2_1 {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ) :
    (Submodular v ↔
      ∀ S T : Finset A, ∀ i : A, S ⊆ T → i ∉ T → marg v i T ≤ marg v i S) ∧
    (Submodular v ↔
      ∀ S T : Finset A,
        v T ≤ v S + ∑ i ∈ T \ S, marg v i S - ∑ i ∈ S \ T, marg v i ((S ∪ T).erase i)) := by sorry

end BudgetFeasSubmod.Main
