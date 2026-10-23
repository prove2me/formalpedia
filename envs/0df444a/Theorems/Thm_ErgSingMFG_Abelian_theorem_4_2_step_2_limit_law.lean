-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_4_2_step_2_limit_law
-- name    : ErgSingMFG.Abelian.theorem_4_2_step_2_limit_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:26.55525+00:00
-- url     : https://prove2.me/theorems/840ec069-c004-40b9-97b9-9ba06ed89d10
-- title:
--   Proof of Theorem 4.2, Step 2, p. 20 — a diffusion reflected upward at a is positively recurrent with limit law m′(y)1_{[a,∞)}(y)dy/∫_a^∞ m′
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Assume Assumptions 2.1, 2.2 and the boundary requirements of §2.1, on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion. Let $a>0$, $x>0$, let $\nu$ be a control and $X$ a solution of (2.1) from $x$ under $\nu$, and suppose that $\nu$ reflects $X$ upward at $a$. Then:
--   1. $X$ is positively recurrent: for every level $y\ge a$, the hitting time $\tau_y=\inf\{t\ge0:X_t=y\}$ has $E[\tau_y]<\infty$;
--   2. $X$ has the limiting distribution
--   $$P_{X_\infty}(dy)=\frac{m'(y)\mathbb 1_{[a,\infty)}(y)}{\int_a^\infty m'(z)\,dz}\,dy .$$
--
--   This is the stationary law entering the consistency condition $\theta=\theta(P_{X_\infty})$ of the equilibrium; it is finite by Assumption 2.2 (9.12).
--
--   Differences from the source:
--   - generalization: the process reflected at the barrier x⋆(θ) by the optimal control, under the hypotheses of Theorem 4.2 → any solution of (2.1) whose control reflects it upward at any level a > 0, under Assumptions 2.1, 2.2 and the §2.1 boundary requirements only; reason: the argument uses only the reflection and the speed measure; taking a = x⋆(θ) and the optimal control gives the source’s claim
--   - encoding: “positively recurrent” → E[τ_y] < ∞ for every level y ≥ a, τ_y the hitting time of y; reason: the standard meaning of positive recurrence for a diffusion on [a, ∞)
--   - reading: “admits a limiting distribution P_{X_∞}” (Definitions 3.1(2), 3.2(2)) → a probability measure μ such that the laws of X_t converge weakly to μ (tested against bounded continuous functions); reason: the paper does not define the term; weak convergence of the one-dimensional laws is its standard meaning (paper.md slip 8)
--   - reading: “ν makes the state process reflected upward at the barrier a” → the Skorokhod conditions a.s.: X_t ≥ a for all t, and dν (including the initial jump) charges only times with X_t = a (`ReflAt`); reason: this is (9.11), the paper’s description of the reflecting control
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 20, proof of Theorem 4.2, Step 2, (9.12)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 4.2, Step 2 (p. 20): a solution `X` of (2.1) from `x > 0` whose control
reflects it upward at a level `a > 0` is positively recurrent (every level `y ≥ a` is hit in finite
expected time) and its limiting distribution is `m′(y) 1_{[a,∞)}(y) dy / ∫ₐ^∞ m′(z) dz`. -/
theorem theorem_4_2_step_2_limit_law {Ω : Type} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (h21 : Asm21 m) (h22 : Asm22 m) (hFR : FundReq m) (hS : IsSetting S)
    (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (ν X : ℝ≥0 → Ω → ℝ)
    (hν : IsControl S ν) (hX : IsStateSol m S x ν X) (hrefl : ReflAt S a ν X) :
    (∀ y ≥ a, ∫⁻ ω, hitTime X y ω ∂S.P < ⊤) ∧
    HasLimitLaw S X ((volume.restrict (Ici a)).withDensity
      (fun y => ENNReal.ofReal (mp m y / ∫ z in Ioi a, mp m z))) := by sorry

end ErgSingMFG.Abelian
