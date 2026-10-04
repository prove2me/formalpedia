-- Prove2me | Theorems.Thm_DemandResponse_FirstBest_propA3_Vbar_closed_form
-- name    : DemandResponse.FirstBest.propA3_Vbar_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:18:50.5377+00:00
-- url     : https://prove2.me/theorems/a9500ae8-4292-48cc-aed0-0c8bb76c281e
-- title:
--   Proposition A.3 (i) with p. 28 — V̄ = −exp(−ρ v̄(0, X₀)), v̄(t,x) = δ(T−t)x + ∫ₜᵀ m̄
-- statement:
--   In the demand-response model with $(f-g)(x)=\delta x$, let $\bar V$ be the auxiliary control value of p. 26 and
--   $$\bar m(t)=H_m(\delta(T-t))+H_v\big(-h-\rho\delta^2(T-t)^2\big),\qquad \bar v(t,x)=\delta(T-t)x+\int_t^T\bar m(s)\,ds,$$
--   with $H_m$, $H_v$ the consumer's Hamiltonians (2.9) and $\rho=\frac{rp}{r+p}$. Then
--   $$\bar V=-e^{-\rho\,\bar v(0,X_0)}.$$
--
--   This identifies the value of the reduced control problem in closed form: $\bar v$ solves the HJB equation (A.6), $-\partial_t\bar v=(f-g)+H_m(\bar v_x)+H_v(\bar v_{xx}-\rho\bar v_x^2-h)$ with $\bar v(T,\cdot)=0$, and it is affine in $x$ when $f-g$ is linear.
--
--   **Formalization Note** The statement uses $H_m$ itself, not its closed form, and needs no relation between $\delta$, $T$ and $A_{\max}$. On p. 28 the paper writes $\int_0^t\bar m(s)ds$ and refers twice to "(A.11)"; the terminal condition $\bar v(T,\cdot)=0$ of (A.6) and Proposition 3.1 require $\int_t^T$, and the first-best PDE is (A.6) ((A.11) is the second-best PDE of p. 30). Both are corrected here.
-- source:
--   arXiv:1810.09063v3, Proposition A.3 (i) (p. 27) and Appendix A.2 (p. 28)

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Model
import Definitions.Def_DemandResponse_FirstBest_ClosedForm

namespace DemandResponse.FirstBest

/-- Proposition A.3 (i) with the explicit solution of p. 28 for `(f - g)(x) = δ x`:
`V̄ = -exp(-ρ v̄(0, X₀))`, `v̄(t, x) = δ(T - t)x + ∫ₜᵀ m̄(s) ds`,
`m̄(t) = H_m(δ(T - t)) + H_v(-h - ρδ²(T - t)²)`. -/
theorem propA3_Vbar_closed_form {N d : ℕ} (P : Params N d) :
    Vbar P = ((-Real.exp (-rho P * vbarA6 P 0 P.X₀) : ℝ) : EReal) := by sorry

end DemandResponse.FirstBest
