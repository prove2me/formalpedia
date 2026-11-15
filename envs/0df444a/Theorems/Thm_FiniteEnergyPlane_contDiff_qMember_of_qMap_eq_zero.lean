-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiff_qMember_of_qMap_eq_zero
-- name    : FiniteEnergyPlane.contDiff_qMember_of_qMap_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T10:25:01.963714+00:00
-- url     : https://prove2.me/theorems/7c8b5ab3-79e2-4887-a55c-d1d8ad9c56c3
-- title:
--   Plane maps of small zeros of the weighted Cauchy–Riemann map are smooth and $\bar J$-holomorphic
-- statement:
--   Here $\bar J$, $J_\infty$, $S_\infty$ form a standard tube structure of radius $\rho$ and decay rate $b$ (`IsStdTubeStructure`, `FiniteEnergyPlane_Tube`); $\delta < 0$, $\delta_T \in (\max(\delta, -2\pi), 0)$; $\chi_T$, $\chi_N$ are slope weights with slopes $(\pi, 2\pi + \delta_T)$ and $(\pi, \delta)$, and $\beta$ is a left cut-off (`IsSlopeWeight`, `IsLeftCutoff`, `FiniteEnergyPlane_TubeFamily`). `qMember` and `qFamily` are the plane maps of `FiniteEnergyPlane_QMember`.
--
--   There is $\varepsilon > 0$ such that for every $x \in \mathrm{QDom}$ with $\|x\| < \varepsilon$ and $\mathrm{qMap}\ \bar J\ \chi_T\ \chi_N\ \beta\ x = 0$, the plane map $\mathrm{qMember}\ \chi_T\ \chi_N\ \beta\ x : \mathbb{C} \to \mathbb{C} \times \mathbb{C}$ is $C^\infty$ and $\bar J$-holomorphic on all of $\mathbb{C}$ (`JHolomorphic.IsJHolomorphicOn Jbar univ`).
--
--   **Role.** A property of the plane maps of the weighted cylinder unknowns near $0$, for statements about $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ and their families.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_QMember

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Near `0`, the plane map of every zero of `qMap` is smooth and `Jbar`-holomorphic on `ℂ`. -/
theorem contDiff_qMember_of_qMap_eq_zero (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 →
      ContDiff ℝ ∞ (qMember χT χN β x) ∧
        JHolomorphic.IsJHolomorphicOn Jbar univ (qMember χT χN β x) := by
  sorry

end FiniteEnergyPlane
