-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_proposition_2
-- name    : BudgetAgg.NashChar.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:45.947529+00:00
-- url     : https://prove2.me/theorems/909d2a0f-79a6-4370-8a4d-ae371eab46db
-- title:
--   Proposition 2, p. 16 — with Leontief utilities, NASH satisfies core fair share
-- statement:
--   Let $P$ be a profile with Leontief utilities, and let $q\in\Delta^m$ maximize the Nash product $\prod_{i\in N}u_i$ over $\Delta^m$. Then $q$ satisfies core fair share: no nonempty coalition $N'$ has a $q'\in\Delta^m$ with
--   $$u_i\Big(\tfrac{|N'|}{n}q'+\big(1-\tfrac{|N'|}{n}\big)q''\Big)>u_i(q)\quad\text{for all }q''\in\Delta^m,\ i\in N'.$$
--   Together with Proposition 1 and the group-strategyproofness of NASH it gives the existence half of Theorem 3.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 16, Proposition 2 (proof p. 33, App. E.1)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Proposition 2, p. 16: Nash outcomes satisfy core fair share. -/
theorem proposition_2 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hnash : IsNashOutcome P q.1) : IsCoreFairShare P q := by sorry

end BudgetAgg.NashChar
