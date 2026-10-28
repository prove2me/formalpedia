-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_proposition_3
-- name    : AlmostSSDPortfolio.AASSD.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:48.294651+00:00
-- url     : https://prove2.me/theorems/d612d66c-3fa3-47d7-8122-e955c7bccb7d
-- title:
--   Proposition 3, p. 11 — Σ_s A_{D,s,λ} equals the SSD violation area of F̂^(2)_{D,λ} against G^(2)
-- statement:
--   In the setting of §2–§3.2, let $D$ be a discretization scheme (containing every benchmark return $b_{t'}$), $\lambda\in\Lambda$, and $\hat S_2=\{t\in[a,b]:\hat F^{(2)}_{D,\lambda}(t)>G^{(2)}(t)\}$. Then the approximate SSD violations of Definition 2 add up to the violation area of the interpolated LPM:
--   $$\int_{\hat S_2}\big(\hat F^{(2)}_{D,\lambda}(t)-G^{(2)}(t)\big)\,dt=\sum_{s=1}^{T_D-1}A_{D,s,\lambda}.$$
--
--   This identifies the closed-form quantity used in the definition of AASSD with a geometric area; it is the step to (12a) of the proof of Theorem 1. The requirement that $D$ contain every $b_{t'}$ is essential: it makes $G^{(2)}$ linear on each sub-interval.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 11, Proposition 3

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem proposition_3 {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (D : Discretization S) (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    ∫ t in D.hatS2 lam, (D.hatF2 lam t - S.G2 t) = ∑ s, D.A lam s := by sorry

end AlmostSSDPortfolio.AASSD
