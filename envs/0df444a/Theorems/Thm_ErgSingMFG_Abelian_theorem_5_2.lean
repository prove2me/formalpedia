-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2
-- name    : ErgSingMFG.Abelian.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:09.033732+00:00
-- url     : https://prove2.me/theorems/ebf83797-9ff7-487b-b28f-1ec3e9401e59
-- title:
--   Theorem 5.2, p. 10 — Abelian limit: as r ↓ 0, (x⋆_r, θ⋆_r) → (x⋆_e, θ⋆_e) and rV(x, θ⋆_r; r) → λ⋆(θ⋆_e) (corrected: assumes Assumption 4.1(ii) for r ∈ (0, 1])
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Assume the standing assumptions of §5: Assumptions 2.1, 2.2, 3.3, 4.3 and the boundary requirements of §2.1, together with Assumption 4.1(ii) for every $r\in(0,1]$ (for every $\theta>0$ there is $\widehat x_r(\theta)>0$ such that $\pi_x(x,\theta)-r+b'(x)$ is positive for $x<\widehat x_r(\theta)$, zero at $\widehat x_r(\theta)$ and negative for $x>\widehat x_r(\theta)$; §5 states that Assumption 4.1 holds for every $r>0$), on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion. Let $x>0$. Then:
--   1. for every $r\in(0,1]$ the discounted MFG has an equilibrium $(\nu^{\star,r},\theta^\star_r)$ (Definition 3.1) whose control reflects the state upward at a barrier, and the ergodic MFG has an equilibrium $(\nu^{\star,e},\theta^\star_e)$ (Definition 3.2) whose control reflects the state upward at a barrier;
--   2. for every family $(\nu^{\star,r},\theta^\star_r)_{r\in(0,1]}$ of discounted equilibria reflecting at barriers $x^\star_r$, and every ergodic equilibrium $(\nu^{\star,e},\theta^\star_e)$ reflecting at $x^\star_e$,
--   $$\lim_{r\downarrow0}(x^\star_r,\theta^\star_r)=(x^\star_e,\theta^\star_e)\qquad\text{and}\qquad\lim_{r\downarrow0}r\,V(x,\theta^\star_r;r)=\lambda^\star(\theta^\star_e),$$
--   where $V(x,\theta;r)=\sup_{\nu\in\mathcal A_d}J(x,\nu,\theta;r)$ is the discounted value (9.1) and $\lambda^\star$ the ergodic value (4.2).
--
--   This is the Abelian limit for the stationary mean field games: the discounted equilibria and their rescaled values converge to the ergodic equilibrium and its value as the discount rate vanishes.
--
--   Differences from the source:
--   - reading: “V(x, r; θ⋆_r) the equilibrium value” (p. 10) and V(x, θ⋆_r; r) in the theorem → V(x, θ⋆_r; r) = sup over 𝒜_d of J(x, ·, θ⋆_r; r), the value (9.1); reason: the printed argument order is a slip; by Definition 3.1(1) this equals the equilibrium payoff (paper.md slip 1)
--   - generalization: the limit statement about the equilibria of Theorems 4.2 and 4.4 → in addition, existence of reflecting discounted equilibria for every r ∈ (0, 1] and of a reflecting ergodic equilibrium is asserted; reason: the added conclusion is supplied by Theorems 4.2 and 4.4 and excludes a vacuous family hypothesis; dropping it gives the source’s statement
--   - encoding: x⋆_r, x⋆_e: the barriers of the equilibria → barriers pinned by the reflection property `ReflAt` of the equilibrium controls; the families are arbitrary equilibria indexed by r ∈ (0, 1]; reason: equilibria are unique (Theorems 4.2, 4.4), so any family is the paper’s
--   - correction: “Throughout this section, we let Assumptions 2.1, 2.2, 3.3, and 4.3 hold, so that Assumption 4.1 is also satisfied for any r > 0” → hypotheses 2.1, 2.2, 3.3, 4.3, the §2.1 requirements, and Assumption 4.1(ii) for every r ∈ (0, 1]; reason: the paper asserts that 4.1 follows from 4.3. Part (i) does (r − b′ > 2c), part (ii) does not, and without it the printed theorem fails. Counterexample satisfying Assumptions 2.1, 2.2, 3.3, 4.3 and the §2.1 requirements: b(x) = −x/10, σ(x) = x (geometric Brownian motion, natural boundaries, m′ = 2x^{−2.2}, φ′_r → −∞, ψ′_r → ∞), c = 0.04, π(x, θ) = (1/θ + 1/5)(1 − e^{−θx})/θ (so π_x = (1/θ + 1/5)e^{−θx}, π_xθ < 0, π_x + b′ crosses 0 once for every θ), f(y) = (1 + y)^{1/2}, F(y) = 2 + y (β = 1/2). Since f ≥ 1, every equilibrium mean is θ = F(∫ f dμ) ≥ 3. At r = 1 and θ ≥ 3, π_x ≤ 1/θ + 1/5 < r + 1/10, so for any ν ∈ 𝒜_d, J(x, ν, θ; 1) − J(x, 0, θ; 1) ≤ ((1/θ + 1/5)/1.1 − 1)E∫e^{−s}dν_s, and the zero control is the unique optimum; its state is a geometric Brownian motion tending to 0, whose laws converge to δ_0 ∉ 𝒫(ℝ₊). So no discounted equilibrium exists at r = 1, and the family in the theorem is undefined. The paper’s proof uses Theorem 4.2, hence 4.1, for each r ∈ (0, 1]; part (ii) is added as a hypothesis for exactly those r
--   - encoding: J, G, V and λ⋆ as extended reals → `EReal` values: expectations of the nonnegative profit and cost as `lintegral`s, subtracted in `EReal`, suprema as `EReal` `⨆`; reason: no junk values; on 𝒜_d and 𝒜_e the cost is finite, so the difference is the paper’s
--   - reading: “ν makes the state process reflected upward at the barrier a” → the Skorokhod conditions a.s.: X_t ≥ a for all t, and dν (including the initial jump) charges only times with X_t = a (`ReflAt`); reason: this is (9.11), the paper’s description of the reflecting control
--   - encoding: “the optimally controlled process X^{x,⋆}” and “J(x, ν⋆, θ) ≥ J(x, ν, θ) for any admissible ν” → a carried solution X of (2.1) under ν⋆ from x, compared with every admissible ν′ and every solution X′ of (2.1) under ν′; reason: the solution of (2.1) is unique (strong uniqueness under Assumption 2.1), so carrying it changes nothing
--   - reading: “admits a limiting distribution P_{X_∞}” (Definitions 3.1(2), 3.2(2)) → a probability measure μ such that the laws of X_t converge weakly to μ (tested against bounded continuous functions); reason: the paper does not define the term; weak convergence of the one-dimensional laws is its standard meaning (paper.md slip 8)
--   - encoding: θ = θ(μ) = F(∫_{ℝ₊} f dμ) ∈ [0, ∞], μ ∈ 𝒫(ℝ₊), with θ ∈ ℝ₊ → μ((−∞, 0]) = 0, ∫_{ℝ₊} f dμ < ∞ and θ = F(∫_{ℝ₊} f dμ); reason: θ ∈ ℝ₊ forces the integral to be finite
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 10, Theorem 5.2; proof pp. 23–24 (Appendix 9.4)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace ErgSingMFG.Abelian

/-- Theorem 5.2 (p. 10), the Abelian limit. Under the standing assumptions of §5, for every initial
condition `x > 0`: discounted equilibria with barrier (reflection) controls exist for every
`r ∈ (0, 1]`, and an ergodic one exists; for every family `(ν⋆,r, θ⋆_r)` of discounted equilibria
reflecting at barriers `x⋆_r` and every ergodic equilibrium `(ν⋆,e, θ⋆_e)` reflecting at `x⋆_e`,
`(x⋆_r, θ⋆_r) → (x⋆_e, θ⋆_e)` and `r V(x, θ⋆_r; r) → λ⋆(θ⋆_e)` as `r ↓ 0`. Corrected: the
single-crossing condition Assumption 4.1(ii) for every `r ∈ (0, 1]` (`h41`), which §5 asserts to
follow from Assumption 4.3, is assumed; it does not follow in general (for `b(x) = −x/10`,
`σ(x) = x`, `π_x(x, θ) = (1/θ + 1/5)e^{−θx}`, `f(y) = √(1 + y)`, `F(y) = 2 + y` every equilibrium
mean is `≥ 3`, where at `r = 1` the zero control is the unique optimum and the state tends to `0`,
so no discounted equilibrium exists at `r = 1`). -/
theorem theorem_5_2 {Ω : Type} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h43 : Asm43 m)
    (h41 : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ θ > 0, ∃ xh, xHatProp m r θ xh)
    (hS : IsSetting S) (x : ℝ) (hx : 0 < x) :
    ((∀ r ∈ Ioc (0 : ℝ) 1, ∃ (ν X : ℝ≥0 → Ω → ℝ) (θ a : ℝ),
        IsDiscEq m S r x ν X θ ∧ ReflAt S a ν X) ∧
      ∃ (ν X : ℝ≥0 → Ω → ℝ) (θ a : ℝ), IsErgEq m S x ν X θ ∧ ReflAt S a ν X) ∧
    ∀ (ν X : ℝ → ℝ≥0 → Ω → ℝ) (θ xs : ℝ → ℝ) (νe Xe : ℝ≥0 → Ω → ℝ) (θe xe : ℝ),
      (∀ r ∈ Ioc (0 : ℝ) 1, IsDiscEq m S r x (ν r) (X r) (θ r) ∧ ReflAt S (xs r) (ν r) (X r)) →
      IsErgEq m S x νe Xe θe → ReflAt S xe νe Xe →
      Tendsto (fun r => (xs r, θ r)) (𝓝[>] 0) (𝓝 (xe, θe)) ∧
      Tendsto (fun r : ℝ => (r : EReal) * V m S x (θ r) r) (𝓝[>] 0) (𝓝 (lamStar m S x θe)) := by sorry

end ErgSingMFG.Abelian
