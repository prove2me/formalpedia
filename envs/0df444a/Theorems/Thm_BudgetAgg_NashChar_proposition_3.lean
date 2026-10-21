-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_proposition_3
-- name    : BudgetAgg.NashChar.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:30.161921+00:00
-- url     : https://prove2.me/theorems/b9eb1a4c-2f61-47ab-97cd-f00167f9f456
-- title:
--   Proposition 3, p. 23 — with Leontief utilities, core fair share implies efficiency
-- statement:
--   Let $P$ be a profile with Leontief utilities and $q\in\Delta^m$. If $q$ satisfies core fair share, then $q$ is Pareto efficient:
--   $$q\ \text{core fair share at }P\ \Longrightarrow\ \text{no }q'\in\Delta^m\text{ with }u_i(q')\ge u_i(q)\ \forall i\text{ and }u_{i'}(q')>u_{i'}(q)\text{ for some }i'.$$
--   Core fair share obviously excludes distributions that make every agent strictly better off; for Leontief utilities it also excludes weak Pareto improvements. In the proof of Theorem 3 this supplies the efficiency hypothesis of Lemma 9.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 23, Proposition 3

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Proposition 3, p. 23: core fair share implies efficiency. -/
theorem proposition_3 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (h : IsCoreFairShare P q) : IsEfficient P q := by sorry

end BudgetAgg.NashChar
