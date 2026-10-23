-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_step_12b
-- name    : AlmostSSDPortfolio.AASSD.step_12b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:54.19269+00:00
-- url     : https://prove2.me/theorems/c659c363-9696-4da6-ba8b-8196ef688ab9
-- title:
--   Proof of Theorem 1, step (12b), p. 46 — the true SSD violation area is at most that of F̂^(2)_{D,λ}
-- statement:
--   In the setting of §2–§3.2, let $D$ be a discretization scheme, $\lambda\in\Lambda$, $S_2=\{t\in[a,b]:F^{(2)}_\lambda(t)>G^{(2)}(t)\}$ and $\hat S_2=\{t\in[a,b]:\hat F^{(2)}_{D,\lambda}(t)>G^{(2)}(t)\}$. Then
--   $$\int_{S_2}\big(F^{(2)}_\lambda(t)-G^{(2)}(t)\big)\,dt\ \le\ \int_{\hat S_2}\big(\hat F^{(2)}_{D,\lambda}(t)-G^{(2)}(t)\big)\,dt.$$
--
--   In the proof of Theorem 1 the paper passes from (12a) to (12b), i.e. replaces the denominator $2\int_{\hat S_2}(\hat F^{(2)}_{D,\lambda}-G^{(2)})$ by $2\int_{S_2}(F^{(2)}_\lambda-G^{(2)})$ in an upper bound on $\tau$, "following from Proposition 1"; this denominator comparison is the mathematical content of that step. Combined with Proposition 3 it is also the left inequality of Theorem 2.
--
--   **Formalization Note.** The printed step is an inequality between ratios with a nonnegative numerator; it is stated here as the comparison of the denominators, which avoids Lean's $x/0=0$ convention.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 46, proof of Theorem 1, (12a)–(12b)

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem step_12b {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∫ t in S.S2 lam, (S.F2 lam t - S.G2 t) ≤ ∫ t in D.hatS2 lam, (D.hatF2 lam t - S.G2 t) := by sorry

end AlmostSSDPortfolio.AASSD
