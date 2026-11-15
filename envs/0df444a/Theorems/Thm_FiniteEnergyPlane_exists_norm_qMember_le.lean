-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_norm_qMember_le
-- name    : FiniteEnergyPlane.exists_norm_qMember_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T10:29:34.0892+00:00
-- url     : https://prove2.me/theorems/a24de74a-1052-408a-bc69-968243f15fdd
-- title:
--   Weighted pointwise bounds of the plane maps, linear in the unknown
-- statement:
--   Let $\delta < 0$, $\delta_T \in (\max(\delta, -2\pi), 0)$, let $\chi_T$, $\chi_N$ be slope weights with slopes $(\pi, 2\pi + \delta_T)$ and $(\pi, \delta)$, and let $\beta$ be a left cut-off. Then there is $K > 0$ such that for all $y \in \mathrm{QDom}$ and $z \in \mathbb{C}$, with $G = \mathrm{qMember}\ \chi_T\ \chi_N\ \beta\ y$,
--   $$\|G(z)_1 - z\| \le K\,\|y\|\,(1 + |z|)^{1 + \delta_T/2\pi}, \qquad \|G(z)_2\| \le K\,\|y\|\,(1 + |z|)^{\delta/2\pi}.$$
--
--   **Role.** A property of the plane maps of the weighted cylinder unknowns near $0$, for statements about $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ and their families.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_QMember

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Weighted pointwise bounds of the plane maps, linear in the unknown: the first component
deviates from `z` by at most `K ‖y‖ (1 + |z|)^{1 + δT/2π}`, and the second component is at most
`K ‖y‖ (1 + |z|)^{δ/2π}`. -/
theorem exists_norm_qMember_le (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ K > 0, ∀ (y : QDom) (z : ℂ),
      ‖(qMember χT χN β y z).1 - z‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (1 + δT / (2 * π)) ∧
      ‖(qMember χT χN β y z).2‖ ≤ K * ‖y‖ * (1 + ‖z‖) ^ (δ / (2 * π)) := by
  sorry

end FiniteEnergyPlane
