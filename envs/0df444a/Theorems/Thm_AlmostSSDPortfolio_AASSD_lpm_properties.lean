-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_lpm_properties
-- name    : AlmostSSDPortfolio.AASSD.lpm_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:47.141736+00:00
-- url     : https://prove2.me/theorems/8e815b90-bc9c-41c3-a4b3-0cb7c25958fa
-- title:
--   §2, p. 7 — the first-order LPM F^(2)_λ is nonnegative, nondecreasing and convex
-- statement:
--   In the finite-scenario portfolio model of §2, let $\lambda\in\Lambda$ be a portfolio and let $F^{(2)}_\lambda(z)=\sum_{t=1}^Tp_t\big(z-\sum_i x_{i,t}\lambda_i\big)I_{\lambda,t}(z)$ be the first-order lower partial moment of its return. Then $F^{(2)}_\lambda$ is a nonnegative, nondecreasing and convex function on $\mathbb R$:
--   $$F^{(2)}_\lambda(z)\ge 0\ \ \forall z,\qquad z\le z'\Rightarrow F^{(2)}_\lambda(z)\le F^{(2)}_\lambda(z'),\qquad F^{(2)}_\lambda \text{ convex on } \mathbb R.$$
--
--   Convexity is what makes the chord interpolation $\hat F^{(2)}_{D,\lambda}$ lie above $F^{(2)}_\lambda$ (Proposition 1).
--
--   **Formalization Note.** The standing assumptions and $\lambda\in\Lambda$ are included as the paper's setting; only the nonnegativity of the $p_t$ is needed.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 7, §2 (sentence after the definition of the first-order LPM)

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem lpm_properties {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    (∀ z, 0 ≤ S.F2 lam z) ∧ Monotone (S.F2 lam) ∧ ConvexOn ℝ univ (S.F2 lam) := by sorry

end AlmostSSDPortfolio.AASSD
