-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_isLeftCutoff
-- name    : FiniteEnergyPlane.exists_isLeftCutoff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:12:29.162208+00:00
-- url     : https://prove2.me/theorems/fe19eef6-e39c-429e-9b47-31a854f00fc8
-- title:
--   A smooth cut-off at the left end of the line
-- statement:
--   There is a $C^\infty$ function $\beta : \mathbb{R} \to \mathbb{R}$ with $\beta(s) = 1$ for $s \le -1$ and $\beta(s) = 0$ for $s \ge 0$ (`IsLeftCutoff β`).
--
--   **Role.** A cut-off localizing a constant near the end $s = -\infty$ of the cylinder, which corresponds to $z = 0$ under $z = e^{2\pi(s+it)}$; it enters the parametrization `qMap` of `FiniteEnergyPlane_TubeFamily`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- There is a smooth cut-off equal to `1` on `(-∞, -1]` and to `0` on `[0, ∞)`. -/
theorem exists_isLeftCutoff : ∃ β : ℝ → ℝ, IsLeftCutoff β := by
  sorry

end FiniteEnergyPlane
