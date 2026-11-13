-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_smooth_qPoint_rep
-- name    : FiniteEnergyPlane.exists_smooth_qPoint_rep
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T21:49:46.659206+00:00
-- url     : https://prove2.me/theorems/b0c3733a-8eeb-4eff-92f6-59f6028881c3
-- title:
--   A smooth $L^4$ representative of the weighted $ar J$-Cauchy–Riemann expression
-- statement:
--   Let $\rho, b > 0$, let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure (`IsStdTubeStructure ρ b Jbar Jinf Sinf`), let $\delta < 0$ and $\delta_T \in (\max(\delta, -2\pi), 0)$, and let $\chi_T, \chi_N, \beta$ satisfy `IsSlopeWeight χT π (2π + δT)`, `IsSlopeWeight χN π δ` and `IsLeftCutoff β`. Then there are $\varepsilon > 0$ and a $C^\infty$ map $F : W^{1,4} \times \mathbb{C} \times W^{1,4} \to L^4 \times L^4$ (`QDom → LpCyl 1 4 × LpCyl 1 4`) such that for every $x$ with $\|x\| < \varepsilon$ the two components of $F(x)$ agree almost everywhere on the cylinder with the two components (read in $\mathbb{R}^2$ via `cToVec`) of the pointwise expression `qPoint Jbar χT χN β x`.
--
--   **Role.** `qMap` is defined as the $L^4$ class of `qPoint` (or $0$ off $L^4$). This statement supplies a smooth map that represents it near $0$; in particular `qMap` is $C^\infty$ on a ball around $0$ (`FiniteEnergyPlane_TubeFamily`).
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For a standard tube structure and admissible weights, there is a `C^∞` map
`F : QDom → L⁴ × L⁴` whose two components, at every point `x` of some ball around `0`, are the
`L⁴` classes of the two components of the pointwise expression `qPoint Jbar χT χN β x`. -/
theorem exists_smooth_qPoint_rep (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ F : QDom → LpCyl 1 4 × LpCyl 1 4, ContDiff ℝ ∞ F ∧ ∀ x ∈ ball (0 : QDom) ε,
      ((F x).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] (fun q => cToVec (qPoint Jbar χT χN β x q).1) ∧
      ((F x).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] (fun q => cToVec (qPoint Jbar χT χN β x q).2) := by
  sorry

end FiniteEnergyPlane
