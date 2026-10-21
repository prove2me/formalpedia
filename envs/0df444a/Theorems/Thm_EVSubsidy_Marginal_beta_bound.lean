-- Prove2me | Theorems.Thm_EVSubsidy_Marginal_beta_bound
-- name    : EVSubsidy.Marginal.beta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:31.338334+00:00
-- url     : https://prove2.me/theorems/960fb1de-7e8a-4255-ae58-e31ca363d707
-- title:
--   Proof of Theorem 3, p. S11 — lower bound on usage-subsidy GSS derivative
-- statement:
--   Suppose $k_As_A\geq k_Bs_B$, the policy mix $(\beta,\gamma)$ lies in the positive pile regime, and both purchase thresholds are positive. The derivative of equilibrium gross social surplus with respect to the usage subsidy exists and obeys
--
--   $$
--   \frac{\partial GSS}{\partial\beta}
--   \geq\sum_{i=A,B}\left(\theta T+\frac{T}{a}\right)
--   \frac{a\lambda_i k_Bs_B\tau}
--   {T(\beta+f-k_B\tau)^2}.
--   $$
--
--   This is the lower estimate needed for Theorem 3's comparison of $\beta$ with $\gamma$.
--
--   **Formalization Note** The derivative is taken of the equilibrium closed form that the preceding surplus identity proves equal to the original $GSS$.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), p. S11 (PDF 43), proof of Theorem 3, lower bound on ∂GSS/∂β

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

namespace EVSubsidy.Marginal

theorem beta_bound (P : Params) (β γ : ℝ) (hP : P.Standing)
    (hks : P.k .B * P.s .B ≤ P.k .A * P.s .A)
    (hω : Regime P (mixBG β γ))
    (hz : ∀ i : Loc, 0 < zStar P (mixBG β γ)
      (xiStar P (mixBG β γ)) i) :
    ∃ d : ℝ,
      HasDerivAt (fun b => GSSClosed P (mixBG b γ)) d β ∧
      (P.θ * P.T + P.T / P.a) *
        (P.a * lam P (mixBG β γ) (xiStar P (mixBG β γ)) .A *
          P.k .B * P.s .B * P.τ /
          (P.T * (β + P.f - P.k .B * P.τ) ^ 2) +
        P.a * lam P (mixBG β γ) (xiStar P (mixBG β γ)) .B *
          P.k .B * P.s .B * P.τ /
          (P.T * (β + P.f - P.k .B * P.τ) ^ 2)) ≤ d := by sorry

end EVSubsidy.Marginal
