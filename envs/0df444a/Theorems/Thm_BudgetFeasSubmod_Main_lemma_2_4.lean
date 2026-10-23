-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_lemma_2_4
-- name    : BudgetFeasSubmod.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:07.721034+00:00
-- url     : https://prove2.me/theorems/a249b0a4-6fca-4cae-bf9f-c9c909f5a380
-- title:
--   Lemma 2.4 (Myerson), p. 6 — a monotone outcome rule with threshold payments is truthful and individually rational
-- statement:
--   Let $A$ be a finite set of agents, $B>0$ a budget, and $f$ a deterministic outcome rule mapping a vector $b\in[0,B]^A$ of declared costs to a set $f(b)\subseteq A$. Suppose $f$ is monotone: if $i\in f(b)$ and $0\le b_i'\le b_i$ then $i\in f(b_i',b_{-i})$. Pay each winner its threshold
--   $$
--   p_i(b)=\sup\{b_i'\in[b_i,B] : i\in f(b_i',b_{-i})\}\qquad (i\in f(b)),
--   $$
--   and each loser $0$. Then the mechanism $(f,p)$ is truthful (no agent with true cost in $[0,B]$ gains by declaring any other cost in $[0,B]$, whatever the others declare) and individually rational ($p_i(b)\ge0$ for all $i$, and $p_i(b)\ge b_i$ for every winner).
--
--   This is the characterization that reduces the design of truthful procurement mechanisms to the design of monotone allocation rules; every mechanism in the paper uses these payments.
--
--   **Formalization Note** Only the existence half of Lemma 2.4 is stated; the uniqueness of the payment scheme is not used later and is omitted. Declared costs and misreports range over $[0,B]$ (Remark 2.5), so the printed $\sup_{b_i'\in[c_i,\infty)}$ (where $c$ denotes the declarations) becomes a supremum over $[b_i,B]$. A loser's utility is $0$; the printed $p_i(b)-c_i$ applies to winners.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 6, Lemma 2.4; Remark 2.5, p. 7

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

/-- Lemma 2.4 (Myerson), p. 6, existence part: a monotone outcome rule with threshold payments is
truthful and individually rational (bids in `[0, B]`, Remark 2.5). -/
theorem lemma_2_4 {A : Type} [Fintype A] [DecidableEq A] (f : (A → ℝ) → Finset A) (B : ℝ)
    (hB : 0 < B) (hf : IsMonotoneRule f B) :
    IsTruthful f B ∧ IsIR f B := by sorry

end BudgetFeasSubmod.Main
