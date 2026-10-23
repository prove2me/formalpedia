-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_theorem_4_2_step_2_fixed_point
-- name    : ErgSingMFG.Abelian.theorem_4_2_step_2_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:06.678359+00:00
-- url     : https://prove2.me/theorems/052ab7fc-f950-4184-ba59-32254543cae6
-- title:
--   Proof of Theorem 4.2, Step 2, pp. 20–21 — the consistency equation (9.13) has a unique solution θ⋆ > θ̂ (corrected: adds ∫_a^∞ f m′ < ∞)
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Let $r>0$ and assume Assumptions 2.1, 2.2, 3.3, 4.1 (at rate $r$) and the boundary requirements of §2.1, and assume in addition that $\int_a^\infty f(y)m'(y)\,dy<\infty$ for every $a>0$ (see the correction below). Fix a decreasing fundamental solution $\widehat\varphi_r$ of (2.10), and let $\theta\mapsto x^\star(\theta)>0$ be the zero of $K(\cdot,\theta)$ of (9.7) (with integrable integrand). Then:
--   1. the equation $f(x^\star(\theta))=F^{-1}(\theta)$ has a unique solution $\widehat\theta>0$;
--   2. for every $\theta>0$ the integrand of
--   $$Q(\theta)=\int_{x^\star(\theta)}^\infty\big(f(y)-F^{-1}(\theta)\big)m'(y)\,dy\qquad(9.13)$$
--   is integrable;
--   3. the consistency equation $Q(\theta)=0$ has a unique solution $\theta^\star>0$, and $\theta^\star>\widehat\theta$.
--
--   Together with the verification step, $(x^\star(\theta^\star),\theta^\star)$ gives the discounted equilibrium.
--
--   Differences from the source:
--   - generalization: a unique θ⋆ > θ̂ solving (9.13) → θ⋆ > θ̂ solves (9.13) and is its only solution in ℝ₊; reason: the source shows Q > 0 on (0, θ̂] as part of the same argument; the statement implies the source’s
--   - correction: Theorem 4.2 (and the proof of its Step 2) under Assumptions 2.1, 2.2, 3.3, 4.1 only → adds the hypothesis ∫_a^∞ f(y) m′(y) dy < ∞ for every a > 0; reason: without it the printed statement is false. Counterexample satisfying every printed assumption, with r = 1, c = 0.3: b(x) = 0.4x, σ(x) = x, π(x, θ) = p(x)/θ with p(x) = ∫_0^x t^{−1/2}e^{−t}dt, f(x) = (1 + x)^{1/2}, F(y) = y + y² (β = 1/2; both are C¹ on [0, ∞) with F′, f′ > 0, so the printed Assumption 3.3(i) holds literally). Then m′(x) = 2x^{−1.2} is integrable at ∞ (Assumption 2.2), r − b′ = 0.6 = 2c, π_x − r + b′ = x^{−1/2}e^{−x}/θ − 0.6 crosses 0 once, |π_xθ| m̂′ = 2x^{0.3}e^{−x}/θ² (m̂′ = 2x^{0.8}) satisfies (π-iv), and 0, ∞ are natural for both geometric Brownian motions, with φ′_r → −∞ and ψ′_r → ∞ (exponents 0.1 ± √2.01). But f m′ ≥ 2x^{−0.7} is not integrable at ∞, so ∫_a^∞ (f − F⁻¹(θ)) m′ dy = +∞ for every a, θ: the system (4.1) has no solution, and the stationary law m′1_{[a,∞)}/∫_a^∞ m′ of any reflected state has θ(μ) = F(∞) = ∞ ∉ ℝ₊. Under Assumption 4.3 (the setting of Theorems 4.4 and 5.2) the added hypothesis holds automatically, since b(x) ≤ −cx for large x gives m′(x) ≤ C·(−E′(x))/x with E(x) = exp(−∫^x 2cz/σ²(z)dz)
--   - reading: F⁻¹(θ) for every θ > 0 in Ĝ, Q and Φ → F⁻¹ on [F(0), ∞), extended by 0 on (0, F(0)] (`Finv`); reason: F⁻¹ is undefined below F(0) when F(0) > 0; the extension is continuous, it is the paper’s function when F(0) = 0 (Remark 3.4), and neither f(x⋆(θ)) = F⁻¹(θ) nor Q(θ) = 0 has a root in (0, F(0)] under it (paper.md slip 3)
--   - encoding: x⋆(θ), the unique zero of K(·, θ) from Step 1 → any function xs with xs(θ) > 0, the integrand of K integrable on (xs(θ), ∞), and K(xs(θ), θ) = 0 for every θ > 0; reason: the zero is unique on ℝ₊ (Step 1), so xs is x⋆
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, pp. 20–21, proof of Theorem 4.2, Step 2, (9.13)–(9.15)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems

open Set Filter MeasureTheory
open scoped Topology

namespace ErgSingMFG.Abelian

/-- Proof of Theorem 4.2, Step 2 (pp. 20–21): let `θ ↦ x⋆(θ)` be the zero of `K(·, θ)` of (9.7).
Then `f(x⋆(θ)) = F⁻¹(θ)` has a unique solution `θ̂ > 0`, the function
`Q(θ) = ∫_{x⋆(θ)}^∞ (f(y) − F⁻¹(θ)) m′(y) dy` of (9.13) is well defined for every `θ > 0`, and the
consistency equation `Q(θ) = 0` has a unique solution `θ⋆ > 0`, with `θ⋆ > θ̂`. Corrected: the
hypothesis `hfm` (`∫ₐ^∞ f(y) m′(y) dy < ∞`) is added; without it `Q` is `+∞`. -/
theorem theorem_4_2_step_2_fixed_point (m : Model) (r : ℝ) (hr : 0 < r)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h41 : Asm41 m r)
    (hfm : ∀ a > 0, IntegrableOn (fun y => m.f y * mp m y) (Ioi a))
    (φh : ℝ → ℝ) (hφ : IsDecrFundHat m r φh) (xs : ℝ → ℝ)
    (hxs : ∀ θ > 0, 0 < xs θ ∧ IntegrableOn (fun y => φh y * Pi m y θ r) (Ioi (xs θ)) ∧
      K m φh (xs θ) θ r = 0) :
    (∃ θh > 0, m.f (xs θh) = Finv m θh ∧ (∀ θ > 0, m.f (xs θ) = Finv m θ → θ = θh) ∧
      (∀ θ > 0, IntegrableOn (fun y => (m.f y - Finv m θ) * mp m y) (Ioi (xs θ))) ∧
      ∃ θs, θh < θs ∧ GHat m (xs θs) θs = 0 ∧
        ∀ θ > 0, GHat m (xs θ) θ = 0 → θ = θs) := by sorry

end ErgSingMFG.Abelian
