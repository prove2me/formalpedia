-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_fderiv_qMember_le
-- name    : FiniteEnergyPlane.exists_norm_fderiv_qMember_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T10:35:16.207281+00:00
-- url     : https://prove2.me/theorems/c94498b6-2581-4f8b-9c67-4d34e0bb4742
-- title:
--   Uniform weighted $C^1$ bound of the plane maps of small zeros, linear in the unknown
-- statement:
--   Here $\bar J$, $J_\infty$, $S_\infty$ form a standard tube structure of radius $\rho$ and decay rate $b$ (`IsStdTubeStructure`, `FiniteEnergyPlane_Tube`); $\delta < 0$, $\delta_T \in (\max(\delta, -2\pi), 0)$; $\chi_T$, $\chi_N$ are slope weights with slopes $(\pi, 2\pi + \delta_T)$ and $(\pi, \delta)$, and $\beta$ is a left cut-off (`IsSlopeWeight`, `IsLeftCutoff`, `FiniteEnergyPlane_TubeFamily`). `qMember` and `qFamily` are the plane maps of `FiniteEnergyPlane_QMember`.
--
--   There are $\varepsilon > 0$ and $K \ge 0$ such that for every $x \in \mathrm{QDom}$ with $\|x\| < \varepsilon$ and $\mathrm{qMap}\ \bar J\ \chi_T\ \chi_N\ \beta\ x = 0$, and every $z \in \mathbb{C}$, with $G = \mathrm{qMember}\ \chi_T\ \chi_N\ \beta\ x$,
--   $$\|DG_1(z) - \mathrm{id}\| \le K\,\|x\|, \qquad (1 + |z|)^{1 - \delta/2\pi}\,\|DG_2(z)\| \le K\,\|x\|.$$
--
--   **Role.** A property of the plane maps of the weighted cylinder unknowns near $0$, for statements about $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ and their families.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_QMember

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Near `0`, the plane maps of zeros of `qMap` satisfy a uniform weighted `C¹` estimate, linear in
the unknown: `‖dψ - id‖ ≤ K ‖x‖` and `(1 + |z|)^{1 - δ/2π} ‖dv‖ ≤ K ‖x‖`. -/
theorem exists_norm_fderiv_qMember_le (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ∃ K ≥ 0, ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = 0 → ∀ z : ℂ,
      ‖fderiv ℝ (fun z => (qMember χT χN β x z).1) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ K * ‖x‖ ∧
      (1 + ‖z‖) ^ (1 - δ / (2 * π)) * ‖fderiv ℝ (fun z => (qMember χT χN β x z).2) z‖ ≤
        K * ‖x‖ := by
  sorry

end FiniteEnergyPlane
