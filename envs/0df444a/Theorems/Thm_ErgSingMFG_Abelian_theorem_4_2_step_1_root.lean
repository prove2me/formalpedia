-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_4_2_step_1_root
-- name    : ErgSingMFG.Abelian.theorem_4_2_step_1_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:02.287219+00:00
-- url     : https://prove2.me/theorems/7a0a7a6b-71a5-4ce7-9efd-e58cbfb8eca8
-- title:
--   Proof of Theorem 4.2, Step 1, p. 19 — K(·, θ) of (9.7) has a unique zero x⋆(θ) ∈ (0, x̂_r(θ))
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Let $r>0$ and assume Assumptions 2.1, 2.2, 3.3, 4.1 (at rate $r$) and the boundary requirements of §2.1. Fix $\theta>0$, a decreasing fundamental solution $\widehat\varphi_r$ of (2.10), and the point $\widehat x_r(\theta)$ of Assumption 4.1(ii). Then the integrand of
--   $$K(x,\theta)=\int_x^\infty\widehat\varphi_r(y)\big(\pi_x(y,\theta)-r+b'(y)\big)\widehat m'(y)\,dy\qquad(9.7)$$
--   is integrable on $(x,\infty)$ for every $x>0$, and $K(\cdot,\theta)$ has exactly one zero $x^\star(\theta)$ in $\mathbb R_+$; it lies in $(0,\widehat x_r(\theta))$.
--
--   The zero $x^\star(\theta)$ is the free boundary of the discounted singular-control problem at a frozen mean $\theta$; the equilibrium barrier is $x^\star(\theta^\star_r)$.
--
--   Differences from the source:
--   - generalization: a unique x⋆(θ) ∈ (0, x̂_r(θ)) solving (9.7) → x⋆(θ) ∈ (0, x̂_r(θ)) solves (9.7) and is the only zero of K(·, θ) on all of ℝ₊; reason: the integrand is strictly negative on (x̂_r(θ), ∞), so K < 0 on [x̂_r(θ), ∞); the statement implies the source’s
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 19, proof of Theorem 4.2, Step 1, (9.7)–(9.8)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems

open Set Filter MeasureTheory
open scoped Topology

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 4.2, Step 1 (p. 19): for `r > 0` and `θ > 0`, the function
`K(x, θ) = ∫ₓ^∞ φ̂_r(y)(π_x(y, θ) − r + b′(y)) m̂′(y) dy` of (9.7) is well defined for every `x > 0`
and has a unique zero `x⋆(θ)` on `(0, ∞)`, which lies in `(0, x̂_r(θ))`. -/
theorem theorem_4_2_step_1_root (m : Model) (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h41 : Asm41 m r)
    (φh : ℝ → ℝ) (hφ : IsDecrFundHat m r φh) (xh : ℝ) (hxh : xHatProp m r θ xh) :
    (∀ x > 0, IntegrableOn (fun y => φh y * Pi m y θ r) (Ioi x)) ∧
    ∃ a ∈ Ioo 0 xh, K m φh a θ r = 0 ∧ ∀ a' > 0, K m φh a' θ r = 0 → a' = a := by sorry

end ErgSingMFG.Abelian
