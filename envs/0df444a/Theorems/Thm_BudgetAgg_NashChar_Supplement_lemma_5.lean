-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_lemma_5
-- name    : BudgetAgg.NashChar.Supplement.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:04:27.240393+00:00
-- url     : https://prove2.me/theorems/578a8f37-3adb-4aa7-bde7-9f84c89f2aab
-- title:
--   Lemma 5 (used in the proof of Theorem 2) — ℓ∞ preferences, m = 3, n ≥ 3: no efficient, strategyproof, proportional mechanism
-- statement:
--   Let $n\ge3$ agents and $m=3$ alternatives have **$\ell_\infty$ preferences**: $u_p(q)=-\max_j|p_j-q_j|$. Then no mechanism $f:(\Delta_3)^n\to\Delta_3$ is efficient, strategyproof and proportional.
--
--   $$\neg\big(\text{efficiency}\wedge\text{strategyproofness}\wedge\text{proportionality}\big)\qquad(m=3,\ n\ge 3).$$
--
--   The proof of Theorem 2 extends this case to every $m\ge3$.
--
--   **Formalization Note** Every mechanism on three alternatives is covered; nothing beyond the three axioms is assumed.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: strategyproofness: either u_i(f(P)) > u_i(f(P′)) or u_i(f(P)) = u_i(f(P′)) (Definition 8, |N′| = 1) → u (P i) (f P′) ≤ u (P i) (f P) for every P′ that differs from P only in agent i; reason: the disjunction of > and = is ≥; same instances
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 28, Lemma 5 (App. D)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 5, p. 28: with `ℓ∞` preferences, `m = 3`, `n ≥ 3`, no mechanism is
efficient, strategyproof and proportional. -/
theorem lemma_5 {n : ℕ} (hn : 3 ≤ n) (f : Mechanism n 3) :
    ¬ (IsEfficientMech lInfUtil f ∧ IsStrategyproofFor lInfUtil f ∧ IsProportional f) := by sorry

end BudgetAgg.NashChar.Supplement
