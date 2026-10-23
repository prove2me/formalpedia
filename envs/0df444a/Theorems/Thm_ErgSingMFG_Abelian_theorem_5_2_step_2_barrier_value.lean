-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2_step_2_barrier_value
-- name    : ErgSingMFG.Abelian.theorem_5_2_step_2_barrier_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:05.701764+00:00
-- url     : https://prove2.me/theorems/11fb589f-531c-40dd-b96e-868faaa30b92
-- title:
--   Proof of Theorem 5.2, Step 2, p. 24 — rV(x⋆_r, θ⋆_r; r) = b(x⋆_r) + π(x⋆_r, θ⋆_r)
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Let $r>0$ and assume Assumptions 2.1, 2.2, 3.3, 4.1 (at rate $r$) and the boundary requirements of §2.1, on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion. Let $\theta>0$ and let $x^\star(\theta)>0$ be the zero of $K(\cdot,\theta)$ of (9.7) for a decreasing fundamental solution $\widehat\varphi_r$ (with integrable integrand). Then the discounted value (9.1) at the barrier satisfies
--   $$r\,V(x^\star(\theta),\theta;r)=b(x^\star(\theta))+\pi(x^\star(\theta),\theta).$$
--   At $\theta=\theta^\star_r$ this is $rV(x^\star_r,\theta^\star_r;r)=b(x^\star_r)+\pi(x^\star_r,\theta^\star_r)$.
--
--   This identity, with $0\le V_x\le1$, turns $rV(x,\theta^\star_r;r)$ into $b(x^\star_r)+\pi(x^\star_r,\theta^\star_r)$ plus a term vanishing as $r\downarrow0$.
--
--   Differences from the source:
--   - generalization: at the equilibrium mean θ = θ⋆_r and barrier x⋆_r → at every θ > 0 and the zero x⋆(θ) of K(·, θ); reason: the argument (V(·, θ; r) ∈ C² solves (9.10) with V_x(x⋆(θ)) = 1, V_xx(x⋆(θ)) = 0) holds at every θ; taking θ = θ⋆_r gives the source’s claim
--   - encoding: J, G, V and λ⋆ as extended reals → `EReal` values: expectations of the nonnegative profit and cost as `lintegral`s, subtracted in `EReal`, suprema as `EReal` `⨆`; reason: no junk values; on 𝒜_d and 𝒜_e the cost is finite, so the difference is the paper’s
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 24, proof of Theorem 5.2, Step 2

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 5.2, Step 2 (p. 24): for `r > 0` and `θ > 0`, let `a = x⋆(θ)` be the zero of
`K(·, θ)` of (9.7). Then `r V(x⋆(θ), θ; r) = b(x⋆(θ)) + π(x⋆(θ), θ)`. -/
theorem theorem_5_2_step_2_barrier_value {Ω : Type} [MeasurableSpace Ω] (m : Model)
    (S : Setting Ω) (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h41 : Asm41 m r)
    (hS : IsSetting S) (φh : ℝ → ℝ) (hφ : IsDecrFundHat m r φh) (a : ℝ) (ha : 0 < a)
    (hint : IntegrableOn (fun y => φh y * Pi m y θ r) (Ioi a)) (hroot : K m φh a θ r = 0) :
    (r : EReal) * V m S a θ r = ((m.b a + m.π a θ : ℝ) : EReal) := by sorry

end ErgSingMFG.Abelian
