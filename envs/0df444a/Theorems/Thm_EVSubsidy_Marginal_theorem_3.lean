-- Prove2me | Theorems.Thm_EVSubsidy_Marginal_theorem_3
-- name    : EVSubsidy.Marginal.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:30.376233+00:00
-- url     : https://prove2.me/theorems/1040004e-f4a3-4a64-90e8-84c405f0ffe5
-- title:
--   Theorem 3, p. 19 — marginal effectiveness of EV-purchase and charging-side subsidies
-- statement:
--   Assume the two-location market's standing conditions and $k_As_A\geq k_Bs_B$. Rational expectations equilibria exist on the positive pile regime. At every such equilibrium selection, the following are sufficient conditions for a subsidy instrument to yield at least as much additional gross social surplus for the same marginal subsidy value:
--
--   1. For a nonnegative mix $(\alpha_A,\alpha_B,\gamma)$ with a balanced pile subsidy pair, the purchase subsidy $\gamma$ is at least as effective as the normalized flexible pile subsidy direction when
--   $$
--   \max_{i=A,B}\frac{(k_i-\alpha_i)^2s_i\tau}
--   {k_i[f-(k_i-\alpha_i)\tau]^2}\leq\mu.
--   $$
--   2. For a nonnegative mix $(\beta,\gamma)$, the per-session subsidy $\beta$ is at least as effective as $\gamma$ when
--   $$
--   \frac{k_Bs_B\tau}{(\beta+f-k_B\tau)^2}\geq\mu.
--   $$
--
--   These are local comparisons of gross social surplus, evaluated at the market equilibrium.
--
--   **Formalization Note** The claim concerns every equilibrium selection, and asserts that a selection exists, so it is not vacuous. The derivative comparisons use $d\gamma/d\beta=\mu/T$ and $d\alpha_i=(k_i-\alpha_i)^2/(fk_i)\,dC$. Balanced means no feasible nonnegative pile subsidy pair with the same equilibrium subsidy value gives greater gross social surplus. Positive purchase thresholds at evaluation points and $\theta\geq0$ are explicit; the policy subsidies at the evaluation point are nonnegative.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), p. 19 (PDF 19), Theorem 3, equations (18)–(19)

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

namespace EVSubsidy.Marginal

theorem theorem_3 (P : Params) (hP : P.Standing)
    (hks : P.k .B * P.s .B ≤ P.k .A * P.s .A) :
    (∃ E, IsEqSelection P E) ∧
    ∀ E, IsEqSelection P E →
      (∀ αA αB γ : ℝ, 0 ≤ αA → 0 ≤ αB → 0 ≤ γ →
        Regime P (mixAG αA αB γ) → Balanced P E αA αB γ →
        (∀ i : Loc, 0 < zStar P (mixAG αA αB γ)
          (E (mixAG αA αB γ)).1 i) →
        max ((P.k .A - αA) ^ 2 * P.s .A * P.τ /
          (P.k .A * (P.f - (P.k .A - αA) * P.τ) ^ 2))
            ((P.k .B - αB) ^ 2 * P.s .B * P.τ /
          (P.k .B * (P.f - (P.k .B - αB) * P.τ) ^ 2)) ≤ P.μ →
        GammaMarginallyBeatsAlphaFlex P E αA αB γ) ∧
      (∀ β γ : ℝ, 0 ≤ β → 0 ≤ γ → Regime P (mixBG β γ) →
        (∀ i : Loc, 0 < zStar P (mixBG β γ)
          (E (mixBG β γ)).1 i) →
        P.μ ≤ P.k .B * P.s .B * P.τ /
          (β + P.f - P.k .B * P.τ) ^ 2 →
        BetaMarginallyBeatsGamma P E β γ) := by sorry

end EVSubsidy.Marginal
