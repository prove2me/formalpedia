-- Prove2me | Theorems.Thm_ConformalBeyondExchangeability_tournament_strange_weight_le
-- name    : ConformalBeyondExchangeability.tournament_strange_weight_le
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:51:33.429481+00:00
-- url     : https://prove2.me/theorems/743d9784-c641-4832-aad0-3646385ce082
-- title:
--   Lemma 2: the weighted fraction of jackknife+ strange points is at most $2\alpha$
-- statement:
--   Let $\tilde w_1,\dots,\tilde w_{n+1}\ge0$ with $\sum_{i=1}^{n+1}\tilde w_i=1$, and let $\alpha\in(0,1)$. For a matrix $r\in\mathbb R^{(n+1)\times(n+1)}$ let
--   $$\mathcal S(r)=\Big\{i\in[n+1]:\sum_{j=1}^{n+1}\tilde w_j\,\mathbb 1\{r_{ij}>r_{ji}\}\ge1-\alpha\Big\}.$$
--   Then for all $r$,
--   $$\sum_{i\in\mathcal S(r)}\tilde w_i\le2\alpha.$$
--
--   This weighted form of Landau's theorem on tournaments is the deterministic step behind the factor $2\alpha$ of the jackknife+.
--
--   **Formalization Note** The paper's hypothesis reads $\sum_{i=1}^{n+1}\tilde w_{n+1}=1$, a typo for $\sum_{i=1}^{n+1}\tilde w_i=1$, which is the normalization its proof uses.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Appendix E.4.2, Lemma 2, eq. (39), p. 51; proof in Appendix E.4.3, p. 52

import Mathlib
import Definitions.Def_ConformalBeyondExchangeability_Basic

open MeasureTheory

namespace ConformalBeyondExchangeability

theorem tournament_strange_weight_le {n : ℕ} (p : Fin (n + 1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (r : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∑ i ∈ tournamentStrangeSet p α r, p i ≤ 2 * α := by sorry

end ConformalBeyondExchangeability
