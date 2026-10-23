-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_4_2_step_1_verification
-- name    : ErgSingMFG.Abelian.theorem_4_2_step_1_verification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:02.193229+00:00
-- url     : https://prove2.me/theorems/d36d5e47-9cdb-4fc6-a03c-e9fc2029269b
-- title:
--   Proof of Theorem 4.2, Step 1, pp. 19–20 — V(·, θ; r) is the C² candidate (9.2), solves HJB (9.10), and reflection at x⋆(θ) is in 𝒜_d and optimal (corrected: sign of (9.10))
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Let $r>0$ and assume Assumptions 2.1, 2.2, 3.3, 4.1 (at rate $r$) and the boundary requirements of §2.1, on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion. Let $\theta>0$, let $x^\star(\theta)>0$ be the zero of $K(\cdot,\theta)$ of (9.7) for a decreasing fundamental solution $\widehat\varphi_r$ (with integrable integrand), and let $\varphi_r$ be a decreasing fundamental solution of (2.9). Write $\bar v(x,\theta)=E_x[\int_0^\infty e^{-rs}\pi(X_s,\theta)ds]$ for the expected discounted profit of the uncontrolled process and $V(x,\theta;r)=\sup_{\nu\in\mathcal A_d}J(x,\nu,\theta;r)$ for the value (9.1). Then:
--   1. $\bar v(\cdot,\theta)$ and $V(\cdot,\theta;r)$ are finite on $\mathbb R_+$;
--   2. $V(\cdot,\theta;r)\in C^2(\mathbb R_+)$ and it solves the HJB equation (9.10), with the sign of a maximisation problem,
--   $$\max\big\{(\mathcal L_X-r)u(x,\theta)+\pi(x,\theta),\,u_x(x,\theta)-1\big\}=0,\qquad x>0;$$
--   3. $V$ is the candidate value (9.2): for some constant $A$,
--   $$V(x,\theta;r)=\begin{cases}A\varphi_r(x)+\bar v(x,\theta),&x>x^\star(\theta),\\(x-x^\star(\theta))+V(x^\star(\theta),\theta;r),&0<x\le x^\star(\theta);\end{cases}$$
--   4. for every initial condition $x>0$ there is a control reflecting the state process upward at $x^\star(\theta)$ (with its solution of (2.1)), and every such control belongs to $\mathcal A_d$ and is optimal: $J(x,\nu,\theta;r)=V(x,\theta;r)$.
--
--   This is the verification step that identifies the optimal control at a frozen mean as reflection at the free boundary $x^\star(\theta)$.
--
--   Differences from the source:
--   - correction: (9.10) printed as min{(𝓛_X − r)u + π, 1 − u_x} = 0 → max{(𝓛_X − r)u + π, u_x − 1} = 0; reason: the printed form is false for the candidate v of (9.2), which the page says solves it. On (0, x⋆(θ)) v_x = 1 and g(x) := (𝓛_X − r)v + π = b(x) − r v(x) + π(x, θ) satisfies g(x⋆(θ)) = 0 (the C² fit with the continuation region, where (𝓛_X − r)v + π = 0) and g′ = π_x − r + b′ > 0 on (0, x̂_r(θ)) ∋ x⋆(θ) (Assumption 4.1(ii)); so g < 0 on (0, x⋆(θ)) and min{g, 1 − v_x} = g < 0. This holds in every instance, e.g. the benchmark b(x) = −x/10, σ(x) = x, π(x, θ) = x^{1/2}θ^{−3/2}. The max form is the standard HJB of a singular control maximisation and is what the proof uses (V_x ≤ 1, p. 24)
--   - encoding: v of (9.2) with the constant A of (9.3), and “v(x, θ) = V(x, θ)” → V finite and C² on ℝ₊, and V = Aφ_r + v̄ on (x⋆(θ), ∞), V(x) = (x − x⋆(θ)) + V(x⋆(θ)) on (0, x⋆(θ)] for some constant A; reason: A is fixed by the C² fit at x⋆(θ) (the first-derivative fit alone determines it since φ′_r < 0), which is how (9.3) defines it; so V equals the paper’s v exactly
--   - encoding: v̄(x, θ) = E_x[∫_0^∞ e^{−rs} π(X_s, θ) ds] along the uncontrolled process X = X⁰ → `vbar`: the EReal supremum of the zero-control payoff J over the solutions of (2.1) from x with ν ≡ 0; reason: all such solutions give the same value (strong uniqueness); the finiteness conclusion also asserts that a solution exists
--   - encoding: “the control ν⋆(θ) such that (9.11) belongs to 𝒜_d and is optimal” → a reflecting control exists from every x > 0, and every control reflecting at x⋆(θ) with its solution of (2.1) is in 𝒜_d and attains V(x, θ; r); reason: the reflecting control is unique up to indistinguishability (Skorokhod problem, cited p. 20), so “the” control and “every” such control are the same statement
--   - encoding: φ_r, the decreasing fundamental solution of (2.9), defined up to a positive factor → every positive C² solution of (2.9) on ℝ₊ tending to 0 at +∞ (`IsDecrFund`); reason: the conclusion “for some constant A” is invariant under rescaling φ_r
--   - reading: “ν makes the state process reflected upward at the barrier a” → the Skorokhod conditions a.s.: X_t ≥ a for all t, and dν (including the initial jump) charges only times with X_t = a (`ReflAt`); reason: this is (9.11), the paper’s description of the reflecting control
--   - encoding: J, G, V and λ⋆ as extended reals → `EReal` values: expectations of the nonnegative profit and cost as `lintegral`s, subtracted in `EReal`, suprema as `EReal` `⨆`; reason: no junk values; on 𝒜_d and 𝒜_e the cost is finite, so the difference is the paper’s
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, pp. 18–20, proof of Theorem 4.2, Step 1, (9.1)–(9.3), (9.10)–(9.11)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 4.2, Step 1 (pp. 19–20), the verification step: for `r > 0` and `θ > 0`, let
`a = x⋆(θ)` be the zero of `K(·, θ)` of (9.7). Then `v̄(·, θ)` is finite, the value `V(·, θ; r)` of
(9.1) is finite and `C²` on `ℝ₊`, solves the HJB equation (9.10) in its correct sign,
`max{(𝓛_X − r)u + π, u_x − 1} = 0`, and is the candidate (9.2):
`V = Aφ_r + v̄` on `(x⋆(θ), ∞)` and `V(x) = (x − x⋆(θ)) + V(x⋆(θ))` on `(0, x⋆(θ)]`; moreover, from
every `x > 0` a control reflecting the state upward at `x⋆(θ)` exists, and every such control
belongs to `𝒜_d` and is optimal. Corrected: the printed (9.10) reads
`min{(𝓛_X − r)u + π, 1 − u_x} = 0`, which the candidate (9.2) violates on `(0, x⋆(θ))`: there
`u_x = 1` and `(𝓛_X − r)u + π = b − r u + π` vanishes at `x⋆(θ)` and has derivative
`π_x − r + b′ > 0` below `x̂_r(θ) > x⋆(θ)`, so it is `< 0`. -/
theorem theorem_4_2_step_1_verification {Ω : Type} [MeasurableSpace Ω] (m : Model)
    (S : Setting Ω) (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h41 : Asm41 m r)
    (hS : IsSetting S) (φh : ℝ → ℝ) (hφh : IsDecrFundHat m r φh) (a : ℝ) (ha : 0 < a)
    (hint : IntegrableOn (fun y => φh y * Pi m y θ r) (Ioi a)) (hroot : K m φh a θ r = 0)
    (φ : ℝ → ℝ) (hφ : IsDecrFund m r φ) :
    (∀ y > 0, vbar m S y θ r ≠ ⊤ ∧ vbar m S y θ r ≠ ⊥) ∧
    (∀ y > 0, V m S y θ r ≠ ⊤ ∧ V m S y θ r ≠ ⊥) ∧
    ContDiffOn ℝ 2 (fun y => (V m S y θ r).toReal) (Ioi 0) ∧
    (∀ y > 0, max (genX m (fun z => (V m S z θ r).toReal) y - r * (V m S y θ r).toReal + m.π y θ)
      (derivWithin (fun z => (V m S z θ r).toReal) (Ioi 0) y - 1) = 0) ∧
    (∃ A : ℝ, (∀ y > a, (V m S y θ r).toReal = A * φ y + (vbar m S y θ r).toReal) ∧
      ∀ y ∈ Ioc 0 a, (V m S y θ r).toReal = (y - a) + (V m S a θ r).toReal) ∧
    ∀ x > 0, (∃ ν X : ℝ≥0 → Ω → ℝ, IsControl S ν ∧ IsStateSol m S x ν X ∧ ReflAt S a ν X) ∧
      ∀ ν X : ℝ≥0 → Ω → ℝ, IsControl S ν → IsStateSol m S x ν X → ReflAt S a ν X →
        Ad S r ν ∧ J m S r θ ν X = V m S x θ r := by sorry

end ErgSingMFG.Abelian
