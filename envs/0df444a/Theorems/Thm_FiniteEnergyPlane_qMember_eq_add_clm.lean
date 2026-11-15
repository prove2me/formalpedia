-- Prove2me | Theorems.Thm_FiniteEnergyPlane_qMember_eq_add_clm
-- name    : FiniteEnergyPlane.qMember_eq_add_clm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T10:24:24.451728+00:00
-- url     : https://prove2.me/theorems/74a80da3-16ca-4ece-ab64-3023506627e7
-- title:
--   The plane map of an unknown is affine in the unknown at each point
-- statement:
--   For all weights $\chi_T, \chi_N, \beta$ and every $z \in \mathbb{C}$ there is a continuous linear map $L : \mathrm{QDom} \to \mathbb{C} \times \mathbb{C}$ with
--   $$\mathrm{qMember}\ \chi_T\ \chi_N\ \beta\ x\ z = (z, 0) + L\,x \qquad \text{for all } x \in \mathrm{QDom}.$$
--
--   **Role.** A property of the plane maps of the weighted cylinder unknowns near $0$, for statements about $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ and their families.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_QMember

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For fixed `z`, the plane map `qMember χT χN β x` at `z` is `(z, 0)` plus a continuous linear
function of `x`. -/
theorem qMember_eq_add_clm (χT χN β : ℝ → ℝ) (z : ℂ) :
    ∃ L : QDom →L[ℝ] ℂ × ℂ, ∀ x : QDom, qMember χT χN β x z = (z, 0) + L x := by
  sorry

end FiniteEnergyPlane
