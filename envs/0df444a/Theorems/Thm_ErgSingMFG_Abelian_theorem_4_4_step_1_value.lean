-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_4_4_step_1_value
-- name    : ErgSingMFG.Abelian.theorem_4_4_step_1_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:11.492713+00:00
-- url     : https://prove2.me/theorems/b26b5383-3728-489d-adac-8a782e46541b
-- title:
--   Proof of Theorem 4.4, Step 1, p. 22 — λ⋆(θ) = b(x⋆(θ)) + π(x⋆(θ), θ), and reflection at x⋆(θ) is optimal
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Assume Assumptions 2.1, 2.2, 3.3, 4.3 and the boundary requirements of §2.1, on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion. Let $x>0$, $\theta>0$, and let $x^\star(\theta)>0$ solve (9.17) for a decreasing fundamental solution $\widehat\varphi_0$ (with integrable integrand). Then:
--   1. the ergodic value (4.2) is
--   $$\lambda^\star(\theta)=b(x^\star(\theta))+\pi(x^\star(\theta),\theta);$$
--   2. there is a control reflecting the state process upward at $x^\star(\theta)$ (together with its solution of (2.1) from $x$);
--   3. every such control belongs to $\mathcal A_e$ and is optimal: its ergodic payoff $G(x,\nu,\theta)$ equals $\lambda^\star(\theta)$.
--
--   This is the verification step of the ergodic problem at a frozen mean.
--
--   Differences from the source:
--   - encoding: “the control ν(x⋆(θ)) ∈ 𝒜_e that keeps the state process above x⋆(θ)” is optimal → a reflecting control exists, and every control reflecting at x⋆(θ) with its solution of (2.1) is in 𝒜_e and attains λ⋆(θ); reason: the reflecting control is unique up to indistinguishability (Skorokhod problem), so “the” control and “every” such control are the same statement
--   - encoding: λ⋆(θ) of (4.2), written without the initial condition → λ⋆ computed with the initial condition x of the statement (`lamStar m S x θ`); reason: (4.2) carries E_x; the conclusion shows the value does not depend on x
--   - reading: “ν makes the state process reflected upward at the barrier a” → the Skorokhod conditions a.s.: X_t ≥ a for all t, and dν (including the initial jump) charges only times with X_t = a (`ReflAt`); reason: this is (9.11), the paper’s description of the reflecting control
--   - encoding: J, G, V and λ⋆ as extended reals → `EReal` values: expectations of the nonnegative profit and cost as `lintegral`s, subtracted in `EReal`, suprema as `EReal` `⨆`; reason: no junk values; on 𝒜_d and 𝒜_e the cost is finite, so the difference is the paper’s
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 22, proof of Theorem 4.4, Step 1

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 4.4, Step 1 (p. 22): for `θ > 0`, let `a = x⋆(θ)` solve (9.17). Then a control
reflecting the state upward at `a` exists; every such control is in `𝒜_e` and optimal for the
ergodic problem (4.2), and `λ⋆(θ) = b(x⋆(θ)) + π(x⋆(θ), θ)`. -/
theorem theorem_4_4_step_1_value {Ω : Type} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h43 : Asm43 m)
    (hS : IsSetting S) (x θ : ℝ) (hx : 0 < x) (hθ : 0 < θ)
    (φh : ℝ → ℝ) (hφ : IsDecrFundHat m 0 φh) (a : ℝ) (ha : 0 < a)
    (hint : IntegrableOn (fun y => φh y * Pi m y θ 0) (Ioi a)) (hroot : K m φh a θ 0 = 0) :
    lamStar m S x θ = ((m.b a + m.π a θ : ℝ) : EReal) ∧
    (∃ ν X : ℝ≥0 → Ω → ℝ, IsControl S ν ∧ IsStateSol m S x ν X ∧ ReflAt S a ν X) ∧
    ∀ ν X : ℝ≥0 → Ω → ℝ, IsControl S ν → IsStateSol m S x ν X → ReflAt S a ν X →
      Ae S ν ∧ G m S θ ν X = lamStar m S x θ := by sorry

end ErgSingMFG.Abelian
