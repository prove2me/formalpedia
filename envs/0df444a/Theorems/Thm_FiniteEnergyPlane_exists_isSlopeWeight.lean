-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_isSlopeWeight
-- name    : FiniteEnergyPlane.exists_isSlopeWeight
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:06:45.512739+00:00
-- url     : https://prove2.me/theorems/7282727b-afd8-4f3d-897f-41b378139685
-- title:
--   Smooth weights with prescribed slopes at both ends
-- statement:
--   For all $a, b \in \mathbb{R}$ there is a $C^\infty$ function $\chi : \mathbb{R} \to \mathbb{R}$ with $\chi'(s) = a$ for $s \le -1$ and $\chi'(s) = b$ for $s \ge 1$ (`IsSlopeWeight χ a b`).
--
--   **Role.** Such $\chi$ define exponential weights $e^{\chi(s)}$ on the cylinder $\mathbb{R} \times S^1$ with different rates at the two ends, as used for the weighted Sobolev spaces of `FiniteEnergyPlane_TubeFamily`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For all slopes `a, b` there is a smooth weight with slope `a` on `(-∞, -1]` and slope `b` on
`[1, ∞)`. -/
theorem exists_isSlopeWeight (a b : ℝ) : ∃ χ : ℝ → ℝ, IsSlopeWeight χ a b := by
  sorry

end FiniteEnergyPlane
