-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_theorem_2
-- name    : BudgetAgg.NashChar.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:04:58.924596+00:00
-- url     : https://prove2.me/theorems/383e4a2e-9a0a-4f2d-a035-3b053a4c0137
-- title:
--   Theorem 2 — with ℓ∞ preferences, m ≥ 3, n ≥ 3, no mechanism is efficient, strategyproof and proportional
-- statement:
--   Let $n\ge3$ agents and $m\ge3$ alternatives have **$\ell_\infty$ preferences**: an agent with peak $p$ has utility $u_p(q)=-\max_{j}|p_j-q_j|$. Then no mechanism $f:(\Delta_m)^n\to\Delta_m$ is efficient, strategyproof and proportional.
--
--   $$\neg\big(\text{efficiency}\wedge\text{strategyproofness}\wedge\text{proportionality}\big)\qquad(m\ge 3,\ n\ge 3).$$
--
--   This is a companion theorem: the goal (Theorem 3) is not proved from it. Its proof rests on Lemma 5 (the case $m=3$).
--
--   **Formalization Note** The statement quantifies over every mechanism, every $m\ge3$ and every $n\ge3$.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: strategyproofness: either u_i(f(P)) > u_i(f(P′)) or u_i(f(P)) = u_i(f(P′)) (Definition 8, |N′| = 1) → u (P i) (f P′) ≤ u (P i) (f P) for every P′ that differs from P only in agent i; reason: the disjunction of > and = is ≥; same instances
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 15, Theorem 2 (proof App. D, pp. 28–30)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 2, p. 15: with `ℓ∞` preferences, `m ≥ 3`, `n ≥ 3`, no mechanism is
efficient, strategyproof and proportional. -/
theorem theorem_2 {n m : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (f : Mechanism n m) :
    ¬ (IsEfficientMech lInfUtil f ∧ IsStrategyproofFor lInfUtil f ∧ IsProportional f) := by sorry

end BudgetAgg.NashChar.Supplement
