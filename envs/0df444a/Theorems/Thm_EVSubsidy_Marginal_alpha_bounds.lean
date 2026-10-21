-- Prove2me | Theorems.Thm_EVSubsidy_Marginal_alpha_bounds
-- name    : EVSubsidy.Marginal.alpha_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:32.339613+00:00
-- url     : https://prove2.me/theorems/3c7df455-816f-49fe-ac2c-6db7fb4df946
-- title:
--   Proof of Theorem 3, p. S11 — arrival-rate bounds in the pile-subsidy direction
-- statement:
--   Consider a balanced interior pile subsidy mix with nonnegative subsidies $(\alpha_A,\alpha_B,\gamma)$ with positive purchase thresholds. Move the two pile subsidies in the paper's normalized direction $d\alpha_i=(k_i-\alpha_i)^2/(fk_i)\,dC$. If, at both locations,
--
--   $$
--   \frac{fs_i\tau}{[f-(k_i-\alpha_i)\tau]^2}
--   \leq\frac{\mu k_i f}{(k_i-\alpha_i)^2},
--   $$
--
--   then the arrival-rate derivatives satisfy
--
--   $$
--   d\lambda_A\leq\lambda_A\frac{a\mu}{T}dC+
--   \lambda_B\phi_A\,d\Delta,
--   \qquad
--   d\lambda_B\leq\lambda_B\frac{a\mu}{T}dC-
--   \lambda_B\phi_A\,d\Delta.
--   $$
--
--   The opposing $d\Delta$ terms describe the shift of B-resident drivers between the two charging locations.
--
--   **Formalization Note** The Lean statement sets $dC=1$ and quantifies the actual derivatives of both arrival rates and the cost difference $\Delta$. Balanced is evaluated using the gross social surplus and subsidy value of an equilibrium selection, as in the source’s marginal pile subsidy argument.
-- source:
--   Zhang & Dou, Coping with Spatial Mismatch: Subsidy Design for Electric Vehicle and Charging Markets, SSRN 3336398 (authors' version), p. S11 (PDF 43), proof of Theorem 3, α-direction arrival-rate bounds

import Mathlib
import Definitions.Def_EVSubsidy_Marginal_Model

namespace EVSubsidy.Marginal

theorem alpha_bounds (P : Params)
    (E : Policy → (Loc → ℝ) × (Loc → ℝ))
    (αA αB γ : ℝ) (hP : P.Standing)
    (hE : IsEqSelection P E)
    (hαA : 0 ≤ αA) (hαB : 0 ≤ αB) (hγ : 0 ≤ γ)
    (hBal : Balanced P E αA αB γ)
    (hω : Regime P (mixAG αA αB γ))
    (hz : ∀ i : Loc, 0 < zStar P (mixAG αA αB γ)
      (xiStar P (mixAG αA αB γ)) i)
    (hc : ∀ i : Loc,
      P.f * P.s i * P.τ /
        (P.f - (P.k i - (mixAG αA αB γ).α i) * P.τ) ^ 2 ≤
      P.μ * P.k i * P.f /
        (P.k i - (mixAG αA αB γ).α i) ^ 2) :
    ∃ dA dB dΔ : ℝ,
      HasDerivAt
        (fun t => lam P
          (mixAG (αA + t * alphaDir P αA αB .A)
            (αB + t * alphaDir P αA αB .B) γ)
          (xiStar P (mixAG
            (αA + t * alphaDir P αA αB .A)
            (αB + t * alphaDir P αA αB .B) γ)) .A) dA 0 ∧
      HasDerivAt
        (fun t => lam P
          (mixAG (αA + t * alphaDir P αA αB .A)
            (αB + t * alphaDir P αA αB .B) γ)
          (xiStar P (mixAG
            (αA + t * alphaDir P αA αB .A)
            (αB + t * alphaDir P αA αB .B) γ)) .B) dB 0 ∧
      HasDerivAt
        (fun t => Delta P (xiStar P
          (mixAG (αA + t * alphaDir P αA αB .A)
            (αB + t * alphaDir P αA αB .B) γ))) dΔ 0 ∧
      dA ≤ lam P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .A *
          (P.a * P.μ / P.T) +
        lam P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .B *
          phi P (xiStar P (mixAG αA αB γ)) .A * dΔ ∧
      dB ≤ lam P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .B *
          (P.a * P.μ / P.T) -
        lam P (mixAG αA αB γ) (xiStar P (mixAG αA αB γ)) .B *
          phi P (xiStar P (mixAG αA αB γ)) .A * dΔ := by sorry

end EVSubsidy.Marginal
