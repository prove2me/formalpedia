-- Prove2me | Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
-- name    : FiniteEnergyPlane.proj_aCoord_exp_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T15:45:46.131138+00:00
-- url     : https://prove2.me/theorems/24a7118f-6efd-4f67-8026-ab38d8088aca
-- title:
--   Radial scaling in symplectization coordinates
-- statement:
--   Let $H$ be a strictly star-shaped level function on $V_n$, and let $y \in V_n$, $y \neq 0$. For every $c \in \mathbb{R}$,
--   $$\mathrm{proj}_H(e^{2c} y) = \mathrm{proj}_H(y), \qquad a_H(e^{2c} y) = a_H(y) + c,$$
--   where $a_H$ is `aCoord H`.
--
--   **Role.** In the identification $V_n \setminus \{0\} \cong \mathbb{R} \times S$, this says that scaling by $e^{2c}$ is the translation by $c$ in the $\mathbb{R}$-direction.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- For `y ≠ 0`, scaling by `e^{2c}` fixes `proj H y` and adds `c` to `aCoord H y`. -/
theorem proj_aCoord_exp_smul {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (c : ℝ) (y : V n) (hy : y ≠ 0) :
    proj H (Real.exp (2 * c) • y) = proj H y ∧ aCoord H (Real.exp (2 * c) • y) = aCoord H y + c := by
  sorry

end FiniteEnergyPlane
