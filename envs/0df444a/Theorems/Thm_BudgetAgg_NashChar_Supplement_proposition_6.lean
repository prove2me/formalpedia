-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_proposition_6
-- name    : BudgetAgg.NashChar.Supplement.proposition_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:06:46.569807+00:00
-- url     : https://prove2.me/theorems/67e6828b-253b-4ae2-8e7a-d4cd976d96c9
-- title:
--   Proposition 6 (used in the proof of Theorem 4) — with Leximin-Leontief preferences, NASH satisfies core fair share
-- statement:
--   Let $P$ be a profile and let $q=\mathrm{NASH}(P)$ be the distribution maximizing the Nash product $\prod_i u_i(q)$ of the Leontief utilities $u_i(q)=\min_{j:p_{i,j}>0}q_j/p_{i,j}$. Then $q$ satisfies core fair share for **Leximin-Leontief preferences**: there are no nonempty $N'\subseteq N$ and $q'\in\Delta_m$ such that
--
--   $$\tfrac{|N'|}{n}q'+\Big(1-\tfrac{|N'|}{n}\Big)q''\ \succ^{lex}_{p_i}\ q\qquad\text{for every }q''\in\Delta_m\text{ and every } i\in N'.$$
--
--   This extends Proposition 2 to the leximin refinement and gives the core-fair-share half of the "if" direction of Theorem 4.
--
--   **Formalization Note** $n,m\ge1$. The Nash outcome is the published predicate `IsNashOutcome`.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: NASH(P) = argmax_{q∈∆m} ∏_i u_i(q), a distribution → IsNashOutcome P q: q is a distribution maximizing the Nash product; "f = NASH" is ∀ P, IsNashOutcome P (f P); reason: the maximizer is unique (published BudgetAgg.NashChar.nash_unique), so the predicate pins down NASH(P)
--   - reading: core fair share: no blocking coalition N′ ⊆ N (Definition 3) → only nonempty coalitions S are excluded from blocking; reason: for N′ = ∅ the condition "for all i ∈ N′" holds vacuously, so ∅ would block every distribution and no mechanism could satisfy the axiom; the base mission reads Definition 3 the same way
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 41, Proposition 6 (proof pp. 41–42)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Proposition 6, p. 41: with Leximin-Leontief preferences, the Nash outcome
satisfies core fair share. -/
theorem proposition_6 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hnash : IsNashOutcome P q.1) : IsLexCoreFairShare P q := by sorry

end BudgetAgg.NashChar.Supplement
