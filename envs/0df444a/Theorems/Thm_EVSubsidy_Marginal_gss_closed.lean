-- Prove2me | Theorems.Thm_EVSubsidy_Marginal_gss_closed
-- name    : EVSubsidy.Marginal.gss_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:43.308575+00:00
-- url     : https://prove2.me/theorems/a40eca0d-d71e-49b6-87b2-1334fb18ca2b
-- title:
--   Proof of Theorem 3, p. S10 — equilibrium GSS identity
-- statement:
--   Let $(\xi,m)$ be a rational expectations equilibrium in the positive pile regime, with nonnegative purchase thresholds. At that equilibrium the providers break even, and gross social surplus satisfies
--
--   $$
--   GSS(\omega,\xi,m)=\left(\theta T+\frac{T}{a}\right)
--   (\lambda_A(\xi)+\lambda_B(\xi)).
--   $$
--
--   This identity connects the model's integral definition of surplus to the expression used in the marginal comparisons.
--
--   **Formalization Note** The right side uses the unique utilization determined by Theorem 1. Nonnegative purchase thresholds keep the exponential tail integral in the paper's regime.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), p. S10 (PDF 42), proof of Theorem 3, “Note that the GSS …”

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

namespace EVSubsidy.Marginal

theorem gss_closed (P : Params) (ω : Policy) (ξ m : Loc → ℝ)
    (hP : P.Standing) (hω : Regime P ω) (heq : IsRE P ω ξ m)
    (hz : ∀ i : Loc, 0 ≤ zStar P ω ξ i) :
    GSS P ω ξ m = GSSClosed P ω := by sorry

end EVSubsidy.Marginal
