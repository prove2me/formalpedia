-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2_step_1_jacobian
-- name    : ErgSingMFG.Abelian.theorem_5_2_step_1_jacobian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:55.234994+00:00
-- url     : https://prove2.me/theorems/09ca18fa-c9ed-4343-ba1a-455a5faf94a7
-- title:
--   Proof of Theorem 5.2, Step 1, p. 24 — det 𝒥Φ(x, θ; r) > 0 on a neighbourhood of (x⋆_e, θ⋆_e) for r ∈ (−ε, ε)
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Assume Assumptions 2.1, 2.2, 3.3, 4.3 (with constant $c$) and the boundary requirements of §2.1, let $r\mapsto\widehat\varphi_r$, $r\in(-c,1)$, be a family of decreasing fundamental solutions of (2.10), and let $(x^\star_0,\theta^\star_0)$ solve the ergodic system (4.3) (for $\widehat\varphi_0$). Then there are $\varepsilon>0$ with $(-\varepsilon,\varepsilon)\subseteq(-c,1)$ and a neighbourhood $B$ of $(x^\star_0,\theta^\star_0)$ such that, for every $r\in(-\varepsilon,\varepsilon)$ and every $(x,\theta)\in B$, the map $(x,\theta)\mapsto\Phi(x,\theta;r)$ of (5.1) is differentiable at $(x,\theta)$ and
--   $$\det\mathcal J\Phi(x,\theta;r)=\big[\partial_x\widehat K\,\partial_\theta\widehat G-\partial_\theta\widehat K\,\partial_x\widehat G\big](x,\theta;r)>0 .$$
--
--   With Kumagai's implicit function theorem this gives continuity of $r\mapsto(x^\star_r,\theta^\star_r)$ at $r=0$.
--
--   Differences from the source:
--   - encoding: det 𝒥Φ(x, θ; r), the determinant of the Jacobian of partial derivatives → a Fréchet derivative D of (x, θ) ↦ Φ(x, θ; r) at the point, with det D > 0; reason: the paper states Φ(·, ·; r) ∈ C¹(ℝ²₊), so its Jacobian matrix is the matrix of its Fréchet derivative
--   - encoding: (x⋆_0, θ⋆_0) := (x⋆_e, θ⋆_e), the ergodic equilibrium pair → any solution (x₀, θ₀) of the system (4.3) for the given φ̂₀; reason: by Theorem 4.4 the system (4.3) has exactly one solution, the ergodic equilibrium pair
--   - encoding: neighbourhoods (−ε, ε) ⊂ (−c, 1) → 0 < ε ≤ min(c, 1); reason: the same condition
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - reading: F⁻¹(θ) for every θ > 0 in Ĝ, Q and Φ → F⁻¹ on [F(0), ∞), extended by 0 on (0, F(0)] (`Finv`); reason: F⁻¹ is undefined below F(0) when F(0) > 0; the extension is continuous, it is the paper’s function when F(0) = 0 (Remark 3.4), and neither f(x⋆(θ)) = F⁻¹(θ) nor Q(θ) = 0 has a root in (0, F(0)] under it (paper.md slip 3)
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 24, proof of Theorem 5.2, Step 1, (9.27)–(9.31)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems

open Set Filter MeasureTheory
open scoped Topology

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 5.2, Step 1 (p. 24): let `(x⋆₀, θ⋆₀)` solve the ergodic system (4.3). There are
`ε > 0` with `(−ε, ε) ⊆ (−c, 1)` and a neighbourhood `B` of `(x⋆₀, θ⋆₀)` such that, for every
`r ∈ (−ε, ε)`, the map `(x, θ) ↦ Φ(x, θ; r)` is differentiable at every point of `B` with Jacobian
determinant `det 𝒥Φ(x, θ; r) > 0`. -/
theorem theorem_5_2_step_1_jacobian (m : Model)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h43 : Asm43 m)
    (φh : ℝ → ℝ → ℝ) (hφ : ∀ r ∈ Ioo (-m.c) 1, IsDecrFundHat m r (φh r))
    (x₀ θ₀ : ℝ) (hsys : SysAt m (φh 0) 0 x₀ θ₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ m.c ∧ ε ≤ 1 ∧ ∃ B ∈ 𝓝 (x₀, θ₀), ∀ r ∈ Ioo (-ε) ε, ∀ p ∈ B,
      ∃ D : ℝ × ℝ →L[ℝ] ℝ × ℝ, HasFDerivAt (fun q : ℝ × ℝ => Phi m φh q.1 q.2 r) D p ∧
        0 < LinearMap.det (D : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by sorry

end ErgSingMFG.Abelian
