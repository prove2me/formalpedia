-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_4_4
-- name    : ErgSingMFG.Abelian.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:20.010694+00:00
-- url     : https://prove2.me/theorems/501721f9-5410-48c3-91e2-2a3510222514
-- title:
--   Theorem 4.4, p. 9 — ergodic equilibrium: unique θ⋆_e, reflecting barrier x⋆_e < x̂₀(θ⋆_e), (4.3) and (4.4) (corrected: control unique only among reflecting equilibria)
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Assume Assumptions 2.1, 2.2, 3.3, 4.3 and the boundary requirements of §2.1, on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion, and let $x>0$. Then:
--   1. the ergodic MFG has an equilibrium $(\nu^{\star,e},\theta^\star_e)$ for the initial condition $x$ (Definition 3.2) whose control reflects the state process upward at a barrier;
--   2. any two equilibria have the same mean $\theta^\star_e$, and any two equilibria whose controls reflect the state process at a barrier have the same barrier and indistinguishable controls;
--   3. for every equilibrium whose control reflects the state process at a barrier $x^\star_e$: $x^\star_e<\widehat x_0(\theta^\star_e)$; $(x^\star_e,\theta^\star_e)$ solves, for every choice of $\widehat\varphi_0$,
--   $$\int_{x^\star_e}^\infty\widehat\varphi_0(y)\big(\pi_x(y,\theta^\star_e)+b'(y)\big)\widehat m'(y)\,dy=0,\qquad\int_{x^\star_e}^\infty\big(f(y)-F^{-1}(\theta^\star_e)\big)m'(y)\,dy=0;\qquad(4.3)$$
--   and the value of the ergodic MFG at equilibrium is
--   $$\lambda^\star(\theta^\star_e)=b(x^\star_e)+\pi(x^\star_e,\theta^\star_e);\qquad(4.4)$$
--   4. the system (4.3) has at most one solution $(a,\theta)\in\mathbb R_+^2$.
--
--   This is the ergodic counterpart of Theorem 4.2, and it supplies the limit objects of Theorem 5.2.
--
--   Differences from the source:
--   - correction: “there exists a unique equilibrium (ν⋆,e, θ⋆_e). Moreover, the process ν⋆,e reflects the state process at the barrier x⋆_e” → any two equilibria have the same θ; an equilibrium with a reflecting control exists; any two equilibria with reflecting controls have the same barrier and indistinguishable controls (a.s. equal paths); the barrier inequality, (4.3) and (4.4) are stated for every reflecting equilibrium; reason: the ergodic criterion ignores finite-time behaviour, so the control is not unique: if ν⋆,e reflects at x⋆_e from x, the control ν′ = δ + (reflection at x⋆_e from x + δ), δ > 0, is in 𝒜_e, has G(x, ν′, θ⋆_e) = λ⋆(θ⋆_e) (the extra cost δ/T → 0, and the reflected process from x + δ has the same long-run average) and the same limit law, so (ν′, θ⋆_e) is a second equilibrium; ν′ charges t = 0 where X′₀ = x + δ > x⋆_e and later reflects at x⋆_e, so it reflects at no barrier. The paper's proof (p. 22) establishes uniqueness of θ⋆_e and of the reflecting equilibrium, which is what is stated
--   - reading: “ν makes the state process reflected upward at the barrier a” → the Skorokhod conditions a.s.: X_t ≥ a for all t, and dν (including the initial jump) charges only times with X_t = a (`ReflAt`); reason: this is (9.11), the paper’s description of the reflecting control
--   - encoding: “the optimally controlled process X^{x,⋆}” and “J(x, ν⋆, θ) ≥ J(x, ν, θ) for any admissible ν” → a carried solution X of (2.1) under ν⋆ from x, compared with every admissible ν′ and every solution X′ of (2.1) under ν′; reason: the solution of (2.1) is unique (strong uniqueness under Assumption 2.1), so carrying it changes nothing
--   - reading: “admits a limiting distribution P_{X_∞}” (Definitions 3.1(2), 3.2(2)) → a probability measure μ such that the laws of X_t converge weakly to μ (tested against bounded continuous functions); reason: the paper does not define the term; weak convergence of the one-dimensional laws is its standard meaning (paper.md slip 8)
--   - encoding: θ = θ(μ) = F(∫_{ℝ₊} f dμ) ∈ [0, ∞], μ ∈ 𝒫(ℝ₊), with θ ∈ ℝ₊ → μ((−∞, 0]) = 0, ∫_{ℝ₊} f dμ < ∞ and θ = F(∫_{ℝ₊} f dμ); reason: θ ∈ ℝ₊ forces the integral to be finite
--   - encoding: F⁻¹(θ⋆) in the consistency equation of the system → a point z ≥ 0 with F(z) = θ⋆; reason: F is a strictly increasing bijection of [0, ∞) onto [F(0), ∞), so this is exactly F⁻¹(θ⋆) and excludes θ⋆ < F(0) where F⁻¹ is undefined (paper.md slip 3)
--   - encoding: “x⋆ < x̂(θ⋆)” for the point x̂(θ⋆) of Assumption 4.1(ii)/4.3(ii) → x⋆ < x̂ for every x̂ with the single-crossing pattern (`xHatProp`); reason: such a point is unique, so this is the same statement
--   - encoding: λ⋆(θ⋆_e) of (4.2), written without the initial condition → λ⋆ computed with the initial condition x of the statement; reason: (4.2) carries E_x
--   - encoding: J, G, V and λ⋆ as extended reals → `EReal` values: expectations of the nonnegative profit and cost as `lintegral`s, subtracted in `EReal`, suprema as `EReal` `⨆`; reason: no junk values; on 𝒜_d and 𝒜_e the cost is finite, so the difference is the paper’s
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 9, Theorem 4.4; proof pp. 21–22 (Appendix 9.2)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace ErgSingMFG.Abelian

/-- Theorem 4.4 (p. 9), corrected: for every initial condition `x > 0`, the ergodic MFG has an
equilibrium whose control reflects the state at a barrier; any two equilibria have the same mean
`θ⋆_e`; any two equilibria with reflecting controls have the same barrier and indistinguishable
controls; every reflecting equilibrium has its barrier `x⋆_e < x̂₀(θ⋆_e)`, `(x⋆_e, θ⋆_e)` solves the
system (4.3), whose solution in `ℝ₊²` is unique, and the equilibrium value is
`λ⋆(θ⋆_e) = b(x⋆_e) + π(x⋆_e, θ⋆_e)` (4.4). The printed uniqueness of the control is false for the
ergodic criterion: an extra initial jump `δ > 0` followed by reflection at `x⋆_e` costs `δ/T → 0`
and leaves `G` and the limit law unchanged, so it is a second, non-reflecting equilibrium. -/
theorem theorem_4_4 {Ω : Type} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (x : ℝ)
    (hx : 0 < x)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h43 : Asm43 m)
    (hS : IsSetting S) :
    (∃ (ν X : ℝ≥0 → Ω → ℝ) (θ a : ℝ), IsErgEq m S x ν X θ ∧ ReflAt S a ν X) ∧
    (∀ (ν X ν' X' : ℝ≥0 → Ω → ℝ) (θ θ' : ℝ), IsErgEq m S x ν X θ →
      IsErgEq m S x ν' X' θ' → θ = θ') ∧
    (∀ (ν X ν' X' : ℝ≥0 → Ω → ℝ) (θ θ' a a' : ℝ), IsErgEq m S x ν X θ → ReflAt S a ν X →
      IsErgEq m S x ν' X' θ' → ReflAt S a' ν' X' → a = a' ∧ ∀ᵐ ω ∂S.P, ∀ t, ν t ω = ν' t ω) ∧
    (∀ (ν X : ℝ≥0 → Ω → ℝ) (θ a : ℝ), IsErgEq m S x ν X θ → ReflAt S a ν X →
      (∀ xh, xHatProp m 0 θ xh → a < xh) ∧ Sys43 m a θ ∧
        lamStar m S x θ = ((m.b a + m.π a θ : ℝ) : EReal)) ∧
    (∀ φh, IsDecrFundHat m 0 φh → ∀ a θ a' θ' : ℝ,
      SysAt m φh 0 a θ → SysAt m φh 0 a' θ' → a = a' ∧ θ = θ') := by sorry

end ErgSingMFG.Abelian
