-- Prove2me | Theorems.Thm_EVSubsidy_Marginal_gamma_derivative
-- name    : EVSubsidy.Marginal.gamma_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:42.988581+00:00
-- url     : https://prove2.me/theorems/f73afe74-144c-49b0-ac1a-97bb1f184e46
-- title:
--   Proof of Theorem 3, p. S10 — purchase subsidy derivative of arrivals
-- statement:
--   In the positive pile regime, suppose both purchase thresholds are strictly positive. Holding the other policy coordinates fixed, the arrival rate at each location has derivative
--
--   $$
--   \frac{\partial\lambda_i}{\partial\gamma}=a\lambda_i.
--   $$
--
--   Under equal marginal subsidy value, this is the paper's normalized derivative $\partial\lambda_i/((T/\mu)\partial\gamma)=(a\mu/T)\lambda_i$. It is used to compare the purchase subsidy with the charging-side instruments.
--
--   **Formalization Note** Utilization is the closed-form equilibrium utilization and does not depend on $\gamma$. Strictly positive thresholds avoid the CDF's boundary at zero.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), p. S10 (PDF 42), proof of Theorem 3, derivative of λ_i

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

namespace EVSubsidy.Marginal

theorem gamma_derivative (P : Params) (ω : Policy) (i : Loc)
    (hP : P.Standing) (hω : Regime P ω)
    (hz : ∀ j : Loc, 0 < zStar P ω (xiStar P ω) j) :
    HasDerivAt
      (fun g => lam P {ω with γ := g} (xiStar P ω) i)
      (P.a * lam P ω (xiStar P ω) i) ω.γ := by sorry

end EVSubsidy.Marginal
