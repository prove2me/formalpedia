-- Prove2me | Theorems.Thm_EVSubsidy_Marginal_theorem_1
-- name    : EVSubsidy.Marginal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:33.811084+00:00
-- url     : https://prove2.me/theorems/fd874677-1350-43e6-93d9-e07c40978014
-- title:
--   Theorem 1, p. 13 — unique RE equilibrium and utilization formula
-- statement:
--   For the two-location market with the standing parameter assumptions, suppose both locations are in the positive pile regime. There is exactly one rational expectations equilibrium $(\xi,m)$. At that equilibrium, for each location $i$,
--
--   $$
--   \xi_i=\frac{(k_i-\alpha_i)\tau}{\beta+f},
--   \qquad nm_i\xi_i=\tau\lambda_i(\xi).
--   $$
--
--   This gives the equilibrium quantities at which the subsidy comparisons are evaluated.
--
--   **Formalization Note** The interior regime makes both pile counts positive and the utilization formula lie strictly between zero and one.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), p. 13 (PDF 13), Theorem 1, equation (11)

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

namespace EVSubsidy.Marginal

theorem theorem_1 (P : Params) (ω : Policy) (hP : P.Standing)
    (hω : Regime P ω) :
    (∃! em : (Loc → ℝ) × (Loc → ℝ), IsRE P ω em.1 em.2) ∧
    ∀ ξ m : Loc → ℝ, IsRE P ω ξ m →
      ∀ i : Loc, ξ i = xiStar P ω i ∧
        P.n * m i * ξ i = P.τ * lam P ω ξ i := by sorry

end EVSubsidy.Marginal
