-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_claim_1
-- name    : ErrBoundCplx.Cplx.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:00.842652+00:00
-- url     : https://prove2.me/theorems/691e1c6e-2b9f-4b02-97f7-61f2ecfbf197
-- title:
--   Claim 1, proof of Theorem 16 — for λ⁰ > λ¹ > 0 and γ > 0, (I + λ⁰ψ′)⁻¹(γ) < (I + λ¹ψ′)⁻¹(γ)
-- statement:
--   Let $\varphi \in \mathcal K(0, \bar r)$, $0 < r_0 < \bar r$, $\alpha_0 = \varphi(r_0)$, and let $\psi = (\varphi|_{[0, r_0]})^{-1} : [0, \alpha_0] \to [0, r_0]$ satisfy assumption (A) with constant $\ell > 0$. Let $\lambda^0 > \lambda^1 > 0$ and $\gamma > 0$. If $\delta^0, \delta^1 \in [0, \alpha_0]$ satisfy
--   $$\delta^0 + \lambda^0\psi'(\delta^0) = \gamma, \qquad \delta^1 + \lambda^1\psi'(\delta^1) = \gamma,$$
--   that is $\delta^i = (I + \lambda^i\psi')^{-1}(\gamma)$, then
--   $$(I + \lambda^0\psi')^{-1}(\gamma) = \delta^0 < \delta^1 = (I + \lambda^1\psi')^{-1}(\gamma).$$
--
--   A larger proximal step moves a positive point further towards $0$; this is the one-step comparison behind Claim 2.
--
--   **Formalization Note** The resolvent is not built as a function: $(I + \lambda\psi')^{-1}(\gamma)$ is any $\delta \in [0, \alpha_0]$ with $\delta + \lambda\psi'(\delta) = \gamma$ (`IsResolventPoint`), with $\psi'$ the derivative of $\psi$ within $[0, \alpha_0]$. The page writes only $\lambda^0 > \lambda^1$; the positivity $\lambda^1 > 0$ is that of the proximal parameters to which the claim is applied (Claim 2 takes positive sequences).
-- source:
--   arXiv:1510.08234v3, proof of Theorem 16, Claim 1, pp. 18–19

import Mathlib
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_WorstCase
open NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, proof of Theorem 16, Claim 1, pp. 18–19. In the setting of §4.2, for
`λ⁰ > λ¹ > 0` and `γ > 0`: `(I + λ⁰ψ')⁻¹(γ) < (I + λ¹ψ')⁻¹(γ)`, where
`δ = (I + λψ')⁻¹(γ)` means `δ ∈ [0, α₀]` and `δ + λψ'(δ) = γ`. -/
theorem claim_1 (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) (hS : ProfileSetting φ ψ rbar r0 ℓ)
    (lam0 lam1 γ δ0 δ1 : ℝ) (hlam1 : 0 < lam1) (hlam : lam1 < lam0) (hγ : 0 < γ)
    (hδ0 : IsResolventPoint ψ (φ r0) lam0 γ δ0) (hδ1 : IsResolventPoint ψ (φ r0) lam1 γ δ1) :
    δ0 < δ1 := by sorry

end ErrBoundCplx.Cplx
