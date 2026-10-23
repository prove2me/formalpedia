-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2_step_2_gradient
-- name    : ErgSingMFG.Abelian.theorem_5_2_step_2_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:27.284205+00:00
-- url     : https://prove2.me/theorems/a5fc99f1-ef2b-41db-8f7b-ca61ee4e37ed
-- title:
--   Proof of Theorem 5.2, Step 2, p. 24 — V(·, θ⋆_r; r) ∈ C²(ℝ₊) and 0 ≤ V_x(·, θ⋆_r; r) ≤ 1
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Let $r>0$ and assume Assumptions 2.1, 2.2, 3.3, 4.1 (at rate $r$) and the boundary requirements of §2.1, on a filtered probability space satisfying the usual conditions with an $\mathbb F$-Brownian motion. Let $\theta>0$. Then the discounted value $V(\cdot,\theta;r)$ of (9.1) is finite on $\mathbb R_+$, belongs to $C^2(\mathbb R_+)$, and
--   $$0\le V_x(x,\theta;r)\le1\qquad\text{for every }x>0 .$$
--
--   The bound is the domination used to pass to the limit $r\downarrow0$ in (9.32).
--
--   Differences from the source:
--   - generalization: at the equilibrium mean θ = θ⋆_r → at every θ > 0; reason: the comparison argument and the HJB equation (9.10) hold at every θ; taking θ = θ⋆_r gives the source’s claim
--   - encoding: V(·, θ; r) ∈ C²(ℝ₊) and V_x → V finite (neither +∞ nor −∞) on ℝ₊, its real part C² on ℝ₊, and V_x the derivative of the real part; reason: V is EReal-valued in Lean; finiteness makes the real part the paper’s V
--   - encoding: J, G, V and λ⋆ as extended reals → `EReal` values: expectations of the nonnegative profit and cost as `lintegral`s, subtracted in `EReal`, suprema as `EReal` `⨆`; reason: no junk values; on 𝒜_d and 𝒜_e the cost is finite, so the difference is the paper’s
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

/-- Proof of Theorem 5.2, Step 2 (p. 24): for `r > 0` and `θ > 0`, the discounted value
`V(·, θ; r)` of (9.1) is finite on `ℝ₊`, belongs to `C²(ℝ₊)`, and satisfies `0 ≤ V_x(·, θ; r) ≤ 1`. -/
theorem theorem_5_2_step_2_gradient {Ω : Type} [MeasurableSpace Ω] (m : Model)
    (S : Setting Ω) (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h41 : Asm41 m r)
    (hS : IsSetting S) :
    (∀ y > 0, V m S y θ r ≠ ⊤ ∧ V m S y θ r ≠ ⊥) ∧
    ContDiffOn ℝ 2 (fun y => (V m S y θ r).toReal) (Ioi 0) ∧
    ∀ y > 0, 0 ≤ deriv (fun z => (V m S z θ r).toReal) y ∧
      deriv (fun z => (V m S z θ r).toReal) y ≤ 1 := by sorry

end ErgSingMFG.Abelian
