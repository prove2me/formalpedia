-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_exploration_count
-- name    : DynAssortPers.Regret.lemma_exploration_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:16.632976+00:00
-- url     : https://prove2.me/theorems/f20887ec-30e5-4bca-9152-f2cfc54656f8
-- title:
--   p. 48 (corrected) — Algorithm 2 explores at most $Cr(m+n)\log T+1$ times in $T$ rounds
-- statement:
--   Let $C\ge0$, $r\in\mathbb N$ and $T\ge1$. Along every history of $T$ rounds, the number of rounds $t\le T$ at which Algorithm 2 explores — that is, at which its current sample $\mathcal O$ satisfies $|\mathcal O|\le Cr(m+n)\log t$ — is at most
--   $$|T_{\mathrm{explore}}|\le Cr(m+n)\log T+1 .$$
--
--   This deterministic count is the exploration part of the regret bound of Theorem 6.
--
--   **Formalization Note** The page prints $|T_{\mathrm{explore}}|\le C\log(T)+1$; the next display of the page uses $\omega(Cr(m+n)\log(T)+1)$, which is what Algorithm 2's test gives, and that is the statement here. The printed form drops the factor $r(m+n)\ge2$ and undercounts the explorations. The hypothesis $C\ge0$ holds for the choice (12); for $C<0$ the algorithm still explores at round $1$ and the bound fails. The count does not depend on the estimator or the exploitation rule.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 6, p. 48, 'Call the set of times when we explored T_explore, and note |T_explore| ≤ C log(T) + 1' (corrected); Algorithm 2, p. 23

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Algorithm2

namespace DynAssortPers.Regret

/-- Proof of Theorem 6, p. 48, in its corrected form: along every history of `T ≥ 1` rounds,
Algorithm 2 explores at most `C r (m + n) log T + 1` times (`|T_explore| ≤ C r (m + n) log(T) + 1`;
the page prints `C log(T) + 1`). -/
theorem lemma_exploration_count {m n : ℕ} (C : ℝ) (hC : 0 ≤ C) (r : ℕ) (T : ℕ) (hT : 1 ≤ T)
    (h : Fin T → Step m n) :
    (explorationCount C r h : ℝ) ≤ C * r * ((m : ℝ) + n) * Real.log T + 1 := by sorry

end DynAssortPers.Regret
