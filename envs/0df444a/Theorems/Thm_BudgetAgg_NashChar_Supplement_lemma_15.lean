-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_lemma_15
-- name    : BudgetAgg.NashChar.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:13:42.269309+00:00
-- url     : https://prove2.me/theorems/40272c37-deef-4d94-abf2-aaedcba6dce6
-- title:
--   Lemma 15 (used in the proof of Theorem 7) — if q″ ⪰lex_i q′ then q″_y ≥ q′_y for every y ∈ T_{q′,i}
-- statement:
--   Let $q',q''\in\Delta_m$ be distributions and let agent $i$ have peak $p_i$. If $q''\succeq^{lex}_{p_i}q'$, then every alternative critical for $i$ at $q'$ receives at least as much in $q''$:
--
--   $$q''_y\ \ge\ q'_y\qquad\text{for all }y\in T_{q',i}.$$
--
--   It is the key inequality in the proof that NASH is group-strategyproof for Leximin-Leontief preferences (Theorem 7).
--
--   **Formalization Note** The agent enters only through her peak, so the statement is about an arbitrary peak $p\in\Delta_m$.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
--   - encoding: an agent i ∈ N with peak p_i → an arbitrary peak p ∈ ∆m; reason: the statement depends on i only through p_i; every agent has some peak and every peak is possible
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 40, Lemma 15 (proof p. 41)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 15, p. 40: if `q″ ⪰lex_p q′` then every alternative critical at `q′` for
the peak `p` receives at least as much in `q″` as in `q′`. -/
theorem lemma_15 {m : ℕ} (p q₁ q₂ : stdSimplex ℝ (Fin m))
    (h : LexGe p q₂.1 q₁.1) :
    ∀ y ∈ crit p q₁.1, q₁.1 y ≤ q₂.1 y := by sorry

end BudgetAgg.NashChar.Supplement
