-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_proposition_1
-- name    : AlmostSSDPortfolio.AASSD.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:53.165057+00:00
-- url     : https://prove2.me/theorems/a5956429-938d-4c41-a392-6f7e4204409f
-- title:
--   Proposition 1, p. 10 — the interpolated LPM F̂^(2)_{D,λ} lies above F^(2)_λ everywhere
-- statement:
--   In the setting of §2–§3.2, let $D=\{a=d_1<\dots<d_{T_D}=b\}$ be a discretization scheme containing every benchmark return, $\lambda\in\Lambda$ a portfolio, and $\hat F^{(2)}_{D,\lambda}$ the piecewise-linear interpolation (2) of $F^{(2)}_\lambda$ at the grid points. Then
--   $$\hat F^{(2)}_{D,\lambda}(x)\ \ge\ F^{(2)}_\lambda(x)\qquad\text{for all }x\in\mathbb R.$$
--
--   Consequently the approximate SSD violation is never smaller than the true one, which is the inequality (12a)→(12b) of the proof of Theorem 1.
--
--   **Formalization Note.** Outside $[a,b]$ the formalization sets $\hat F^{(2)}_{D,\lambda}=F^{(2)}_\lambda$ (see the definition file), so the inequality there is an equality; the content is on $[a,b]$.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 10, Proposition 1

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem proposition_1 {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∀ x : ℝ, S.F2 lam x ≤ D.hatF2 lam x := by sorry

end AlmostSSDPortfolio.AASSD
