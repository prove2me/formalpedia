-- Prove2me | Theorems.Thm_FiniteEnergyPlane_qMap_smooth_of_isStdTubeStructure
-- name    : FiniteEnergyPlane.qMap_smooth_of_isStdTubeStructure
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:10:22.469606+00:00
-- url     : https://prove2.me/theorems/e19a1e66-f629-462a-9dab-79c6d9b41ec0
-- title:
--   Smoothness and linearization of the weighted $\bar J$-Cauchy–Riemann operator
-- statement:
--   Let $\rho, b > 0$, let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure (`IsStdTubeStructure ρ b Jbar Jinf Sinf`), let $\delta < 0$ and $\delta_T \in (\max(\delta, -2\pi), 0)$, and let $\chi_T, \chi_N, \beta$ satisfy `IsSlopeWeight χT π (2π + δT)`, `IsSlopeWeight χN π δ` and `IsLeftCutoff β`. Then there is $\varepsilon > 0$ such that, with $Q =$ `qMap Jbar χT χN β` $: W^{1,4} \times \mathbb{C} \times W^{1,4} \to L^4 \times L^4$:
--   1. $Q$ is $C^\infty$ on the ball $B_\varepsilon(0)$, and $Q(0) = 0$;
--   2. for every $\zeta \in W^{1,4}$: $\big[DQ(0)(\zeta, 0, 0)\big]_1 = \partial_s\zeta + J_0\partial_t\zeta + \chi_T'(s)\zeta$ a.e., and $\big[DQ(0)(\zeta, 0, 0)\big]_2 = 0$;
--   3. for every $\zeta \in W^{1,4}$: $\big[DQ(0)(0, 0, \zeta)\big]_2 = \partial_s\zeta + J_0\partial_t\zeta + \big(N(s,t) + \chi_N'(s)\big)\zeta$ a.e., where $N =$ `normalCoeff Jbar`.
--
--   **Role.** $Q$ is the nonlinear Cauchy–Riemann operator of $\bar J$ on maps near $z \mapsto (z, 0)$, written in weighted Sobolev coordinates (`FiniteEnergyPlane_TubeFamily`). The statement gives its smoothness and identifies the diagonal blocks of its linearization at the trivial solution as Cauchy–Riemann operators on the cylinder.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For a standard tube structure, `qMap` is `C^∞` on a ball around `0`, vanishes at `0`, and
its derivative at `0` is upper triangular: on tangential directions `(ζ, 0, 0)` its first component
is `∂ₛ + J₀ ∂ₜ + χT'` applied to `ζ` and its second component vanishes; on normal directions
`(0, 0, ζ)` its second component is `∂ₛ + J₀ ∂ₜ + normalCoeff Jbar + χN'` applied to `ζ`. -/
theorem qMap_smooth_of_isStdTubeStructure (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ContDiffOn ℝ ∞ (qMap Jbar χT χN β) (ball 0 ε) ∧ qMap Jbar χT χN β 0 = 0 ∧
      (∀ ζ : ↥(W1p 4 1),
        (((fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
            crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4)) ∧
          (fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).2 = 0) ∧
      ∀ ζ : ↥(W1p 4 1),
        ((fderiv ℝ (qMap Jbar χT χN β) 0 (0, 0, ζ)).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
          crApply (fun x => normalCoeff Jbar x + deriv χN x.1 • (1 : Mat 1)) (ζ : Triple 1 4) := by
  sorry

end FiniteEnergyPlane
