-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_lemma_C_2
-- name    : FoodDeliv.Decentral.lemma_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:04.251456+00:00
-- url     : https://prove2.me/theorems/7b6b123e-006e-42ef-92d5-303a475236f7
-- title:
--   Lemma C.2 (OA p. 8) — customer strategy: the equilibrium joining rates λ_D(p, θ), λ_W(p, θ)
-- statement:
--   Consider the food-delivery model with parameters $R,\mu,c,\phi,\Lambda_0,\Lambda_1$ satisfying the standing assumptions and $\phi>0$. Fix a food price $p$ and a delivery fee $\theta$, and let $(\lambda_D,\lambda_{1W},\lambda_{0W})$ be any customers' equilibrium under $(p,\theta)$, with $\lambda_W=\lambda_{0W}+\lambda_{1W}$. Then:
--
--   1. If $p\le R-\frac{c}{\mu-\Lambda_1}$:
--      - for $0<\theta\le\frac{(c-\phi)(R-p)}{c}$: $\lambda_D=\Lambda_1$ and $\lambda_W=\mu-\frac{c}{R-p}-\Lambda_1$;
--      - for $\frac{(c-\phi)(R-p)}{c}<\theta\le R-p-\frac{\phi}{\mu}$: $\lambda_D=0$ and $\lambda_W=\mu-\frac{c}{R-p}$.
--   2. If $R-\frac{c}{\mu-\Lambda_1}<p\le R-\frac{\phi}{\mu}$:
--      - for $0<\theta\le\max\big(R-p-\frac{\phi}{\mu-\Lambda_1},0\big)$: $\lambda_D=\Lambda_1$, $\lambda_W=0$;
--      - for $\max\big(R-p-\frac{\phi}{\mu-\Lambda_1},0\big)<\theta\le\min\big(\frac{(c-\phi)(R-p)}{c},R-p-\frac{\phi}{\mu}\big)$: $\lambda_D=\mu-\frac{\phi}{R-p-\theta}$, $\lambda_W=0$;
--      - for $\theta>\min\big(\frac{(c-\phi)(R-p)}{c},R-p-\frac{\phi}{\mu}\big)$ and $p\le R-\frac{c}{\mu}$: $\lambda_D=0$, $\lambda_W=\mu-\frac{c}{R-p}$.
--
--   This is the third stage of the game: it pins down the demand the platform and the restaurant face for every price and fee.
--
--   **Formalization Note** The paper states the last row without $p\le R-c/\mu$; for $R-c/\mu<p\le R-\phi/\mu$ it gives a negative $\lambda_W$ (finding F3), and the paper's own derivation (Online Appendix p. 12) covers only $p\le R-c/\mu$ there, so the row is stated on that range. $\phi>0$ is added (findings F5, F7): at $\phi=0$ the delivery utility does not depend on $\lambda$, and at $U_D=0>U_W$ customers may split between delivery and balking, so $\lambda_D$ is not determined. The equilibrium is the model's (optimality conditions with the p. 7 tie rule), not a formula.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), Online Appendix p. 8, Lemma C.2

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

namespace FoodDeliv.Decentral

/-- Lemma C.2 (Customer Strategy), Online Appendix p. 8: every customers' equilibrium under the
food price `p` and delivery fee `θ` has the joining rates `λ_D` and `λ_W` of the table.
The last row is stated for `p ≤ R - c/μ`, the range for which the paper derives it. -/
theorem lemma_C_2 (P : Params) (hP : P.Standing) (hϕ : 0 < P.ϕ) (p θ : ℝ) (s : Profile)
    (hs : IsCustEq P p θ s) :
    (p ≤ P.R - P.c / (P.μ - P.Λ1) →
      (0 < θ ∧ θ ≤ (P.c - P.ϕ) * (P.R - p) / P.c →
        s.lamD = P.Λ1 ∧ s.lamW = P.μ - P.c / (P.R - p) - P.Λ1) ∧
      ((P.c - P.ϕ) * (P.R - p) / P.c < θ ∧ θ ≤ P.R - p - P.ϕ / P.μ →
        s.lamD = 0 ∧ s.lamW = P.μ - P.c / (P.R - p))) ∧
    (P.R - P.c / (P.μ - P.Λ1) < p ∧ p ≤ P.R - P.ϕ / P.μ →
      (0 < θ ∧ θ ≤ max (P.R - p - P.ϕ / (P.μ - P.Λ1)) 0 →
        s.lamD = P.Λ1 ∧ s.lamW = 0) ∧
      (max (P.R - p - P.ϕ / (P.μ - P.Λ1)) 0 < θ ∧
          θ ≤ min ((P.c - P.ϕ) * (P.R - p) / P.c) (P.R - p - P.ϕ / P.μ) →
        s.lamD = P.μ - P.ϕ / (P.R - p - θ) ∧ s.lamW = 0) ∧
      (min ((P.c - P.ϕ) * (P.R - p) / P.c) (P.R - p - P.ϕ / P.μ) < θ →
        p ≤ P.R - P.c / P.μ →
        s.lamD = 0 ∧ s.lamW = P.μ - P.c / (P.R - p))) := by sorry

end FoodDeliv.Decentral
