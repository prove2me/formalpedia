-- Prove2me | Theorems.Thm_FiniteEnergyPlane_contDiffOn_qFamily_of_qMap_eq_zero
-- name    : FiniteEnergyPlane.contDiffOn_qFamily_of_qMap_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T10:33:07.242448+00:00
-- url     : https://prove2.me/theorems/accbbcc4-5360-4d78-8efd-98d9d6d383ee
-- title:
--   Families of plane maps along smooth curves of small zeros are jointly smooth
-- statement:
--   Here $\bar J$, $J_\infty$, $S_\infty$ form a standard tube structure of radius $\rho$ and decay rate $b$ (`IsStdTubeStructure`, `FiniteEnergyPlane_Tube`); $\delta < 0$, $\delta_T \in (\max(\delta, -2\pi), 0)$; $\chi_T$, $\chi_N$ are slope weights with slopes $(\pi, 2\pi + \delta_T)$ and $(\pi, \delta)$, and $\beta$ is a left cut-off (`IsSlopeWeight`, `IsLeftCutoff`, `FiniteEnergyPlane_TubeFamily`). `qMember` and `qFamily` are the plane maps of `FiniteEnergyPlane_QMember`.
--
--   There is $\varepsilon > 0$ such that for every $r > 0$ and every curve $\gamma : \mathbb{R} \to \mathrm{QDom}$ that is $C^\infty$ on $(-r, r)$ with $\|\gamma(t)\| < \varepsilon$ and $\mathrm{qMap}\ \bar J\ \chi_T\ \chi_N\ \beta\ (\gamma(t)) = 0$ for all $t \in (-r, r)$, the family $(z, t) \mapsto \mathrm{qMember}\ \chi_T\ \chi_N\ \beta\ (\gamma(t))\ z$ (`qFamily`) is $C^n$ on $\mathbb{C} \times (-r, r)$ for every $n \in \mathbb{N}$.
--
--   **Role.** A property of the plane maps of the weighted cylinder unknowns near $0$, for statements about $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ and their families.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_QMember

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Near `0`, the family of plane maps along a smooth curve of zeros of `qMap` is jointly `C^n` in
`(z, t)` for every `n`. -/
theorem contDiffOn_qFamily_of_qMap_eq_zero (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∀ r > 0, ∀ γ : ℝ → QDom, ContDiffOn ℝ ∞ γ (Ioo (-r) r) →
      (∀ t ∈ Ioo (-r) r, γ t ∈ ball (0 : QDom) ε ∧ qMap Jbar χT χN β (γ t) = 0) →
      ∀ n : ℕ, ContDiffOn ℝ n (qFamily χT χN β γ) (univ ×ˢ Ioo (-r) r) := by
  sorry

end FiniteEnergyPlane
