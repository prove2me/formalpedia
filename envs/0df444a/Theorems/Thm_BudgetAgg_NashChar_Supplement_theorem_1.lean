-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_theorem_1
-- name    : BudgetAgg.NashChar.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:03:02.461284+00:00
-- url     : https://prove2.me/theorems/503ec8aa-1834-4ef0-8b35-258722ef802a
-- title:
--   Theorem 1 — with ℓ1 preferences, m ≥ 3, n ≥ 3, no mechanism is efficient, strategyproof and proportional
-- statement:
--   Let $n\ge3$ agents and $m\ge3$ alternatives have **$\ell_1$ preferences**: an agent with peak $p\in\Delta_m$ has utility $u_p(q)=-\sum_j|p_j-q_j|$ for a distribution $q$. Then no mechanism $f:(\Delta_m)^n\to\Delta_m$ is simultaneously
--
--   1. efficient (every $f(P)$ is Pareto efficient for these utilities),
--   2. strategyproof (no agent gains by misreporting her peak), and
--   3. proportional ($f(P)_j=\sum_i p_{i,j}/n$ on single-minded profiles).
--
--   $$\neg\big(\text{efficiency}\wedge\text{strategyproofness}\wedge\text{proportionality}\big)\qquad(m\ge 3,\ n\ge 3).$$
--
--   This is a companion theorem of the mission: the goal (Theorem 3) is not proved from it. It shows that the positive result for Leontief utilities does not extend to $\ell_1$ preferences.
--
--   **Formalization Note** The statement quantifies over every mechanism, every $m\ge3$ and every $n\ge3$; no anonymity, neutrality or continuity is assumed.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: strategyproofness: either u_i(f(P)) > u_i(f(P′)) or u_i(f(P)) = u_i(f(P′)) (Definition 8, |N′| = 1) → u (P i) (f P′) ≤ u (P i) (f P) for every P′ that differs from P only in agent i; reason: the disjunction of > and = is ≥; same instances
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 11, Theorem 1 (proof pp. 11–15, App. B)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 1, p. 11: with `ℓ1` preferences, `m ≥ 3`, `n ≥ 3`, no mechanism is
efficient, strategyproof and proportional. -/
theorem theorem_1 {n m : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (f : Mechanism n m) :
    ¬ (IsEfficientMech l1Util f ∧ IsStrategyproofFor l1Util f ∧ IsProportional f) := by sorry

end BudgetAgg.NashChar.Supplement
