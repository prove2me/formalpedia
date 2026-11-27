-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_theorem_7
-- name    : BudgetAgg.NashChar.Supplement.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:14:11.176881+00:00
-- url     : https://prove2.me/theorems/4d794dc7-0cb6-4ef9-adfc-4b9e958f94cb
-- title:
--   Theorem 7 — with Leximin-Leontief preferences, NASH is group-strategyproof
-- statement:
--   Assume Leximin-Leontief preferences. The Nash product rule, $\mathrm{NASH}(P)=\arg\max_{q\in\Delta_m}\prod_i u_i(q)$ with the Leontief utilities $u_i(q)=\min_{j:p_{i,j}>0}q_j/p_{i,j}$, is group-strategyproof for the leximin relations: for every coalition $N'\subseteq N$ and profiles $P,P'$ that agree outside $N'$,
--
--   $$\exists i\in N':\ \mathrm{NASH}(P)\succ^{lex}_{p_i}\mathrm{NASH}(P')\quad\text{or}\quad\forall i\in N':\ \mathrm{NASH}(P)\simeq^{lex}_{p_i}\mathrm{NASH}(P').$$
--
--   This is a companion theorem: the goal (Theorem 3) is not proved from it. It also gives the strategyproofness half of the "if" direction of Theorem 4.
--
--   **Formalization Note** $n,m\ge1$. The rule is any mechanism $g$ whose value at every profile is the Nash outcome; by the published uniqueness of the maximizer this is NASH itself.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: NASH(P) = argmax_{q∈∆m} ∏_i u_i(q), a distribution → IsNashOutcome P q: q is a distribution maximizing the Nash product; "f = NASH" is ∀ P, IsNashOutcome P (f P); reason: the maximizer is unique (published BudgetAgg.NashChar.nash_unique), so the predicate pins down NASH(P)
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 41, Theorem 7 (proof p. 41)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 7, p. 41: with Leximin-Leontief preferences, NASH is group-strategyproof. -/
theorem theorem_7 {n m : ℕ} [NeZero n] [NeZero m]
    (g : Mechanism n m) (hg : ∀ P, IsNashOutcome P (g P).1) :
    IsLexGroupSP g := by sorry

end BudgetAgg.NashChar.Supplement
