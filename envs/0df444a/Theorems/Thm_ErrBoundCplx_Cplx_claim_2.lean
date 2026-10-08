-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_claim_2
-- name    : ErrBoundCplx.Cplx.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:49.353035+00:00
-- url     : https://prove2.me/theorems/a6a1f2fe-888b-488a-ab4b-f9cc4098cd51
-- title:
--   Claim 2, proof of Theorem 16 — proximal sequences with larger steps λ⁰_k ≥ λ¹_k from a common start stay below: β⁰_k ≤ β¹_k
-- statement:
--   Let $\varphi \in \mathcal K(0, \bar r)$, $0 < r_0 < \bar r$, $\alpha_0 = \varphi(r_0)$, and let $\psi = (\varphi|_{[0, r_0]})^{-1} : [0, \alpha_0] \to [0, r_0]$ satisfy assumption (A) with constant $\ell > 0$. Let $(\lambda^0_k)_{k\in\mathbb N}$ and $(\lambda^1_k)_{k\in\mathbb N}$ be positive sequences with $\lambda^0_k \ge \lambda^1_k$ for all $k \ge 0$, and let $(\beta^0_k)$, $(\beta^1_k)$ be the proximal sequences
--   $$\beta^0_{k+1} = (I + \lambda^0_k\psi')^{-1}(\beta^0_k), \qquad \beta^1_{k+1} = (I + \lambda^1_k\psi')^{-1}(\beta^1_k),$$
--   with $\beta^0_0 = \beta^1_0 \in (0, \alpha_0]$. Then
--   $$\beta^0_k \le \beta^1_k \qquad \text{for all } k \ge 0.$$
--
--   In the proof of Theorem 16 this is applied with $\beta^1 = \alpha$ (step $\zeta$) and $\beta^0 = \beta$ (steps $s_k \ge \zeta$), giving $\beta_k \le \alpha_k$ and hence $f(x_k) = \psi(\beta_k) \le \psi(\alpha_k)$.
--
--   **Formalization Note** $\delta = (I + \lambda\psi')^{-1}(\gamma)$ means $\delta \in [0, \alpha_0]$ and $\delta + \lambda\psi'(\delta) = \gamma$, with $\psi'$ the derivative of $\psi$ within $[0, \alpha_0]$. The page prints the initial condition as $\beta^0_0 = \beta^1_0 \in (0, r_0]$; the resolvents act on $[0, \alpha_0] = \operatorname{dom}\psi$ and the claim is applied with $\beta_0 = \alpha_0$, so the interval is $(0, \alpha_0]$ here.
-- source:
--   arXiv:1510.08234v3, proof of Theorem 16, Claim 2, p. 19 (printed '(0, r₀]' read as (0, α₀])

import Mathlib
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_WorstCase
open NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, proof of Theorem 16, Claim 2, p. 19. In the setting of §4.2, let
`(λ⁰_k)`, `(λ¹_k)` be positive sequences with `λ⁰_k ≥ λ¹_k`, and let
`β⁰_{k+1} = (I + λ⁰_kψ')⁻¹(β⁰_k)`, `β¹_{k+1} = (I + λ¹_kψ')⁻¹(β¹_k)` with
`β⁰_0 = β¹_0 ∈ (0, α₀]` (the page prints `(0, r₀]`; the resolvents act on `[0, α₀]`).
Then `β⁰_k ≤ β¹_k` for all `k ≥ 0`. -/
theorem claim_2 (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) (hS : ProfileSetting φ ψ rbar r0 ℓ)
    (lam0 lam1 β0 β1 : ℕ → ℝ) (hlam0 : ∀ k, 0 < lam0 k) (hlam1 : ∀ k, 0 < lam1 k)
    (hlam : ∀ k, lam1 k ≤ lam0 k)
    (hβ0 : ∀ k, IsResolventPoint ψ (φ r0) (lam0 k) (β0 k) (β0 (k + 1)))
    (hβ1 : ∀ k, IsResolventPoint ψ (φ r0) (lam1 k) (β1 k) (β1 (k + 1)))
    (hinit : β0 0 = β1 0) (hinit_mem : β0 0 ∈ Set.Ioc 0 (φ r0)) :
    ∀ k, β0 k ≤ β1 k := by sorry

end ErrBoundCplx.Cplx
