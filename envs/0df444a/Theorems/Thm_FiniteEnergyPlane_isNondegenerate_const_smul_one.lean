-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerate_const_smul_one
-- name    : FiniteEnergyPlane.isNondegenerate_const_smul_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T22:32:20.548839+00:00
-- url     : https://prove2.me/theorems/34b70c1c-3814-4349-8ea6-e8579d0c0f64
-- title:
--   Constant loops c·I with 0 < c < 2π are nondegenerate
-- statement:
--   Let $m \in \mathbb{N}$ and $0 < c < 2\pi$. The constant loop $S(t) = c\,\mathbb{1}$ of real $2m\times 2m$ matrices is a symmetric loop (`IsSymLoop`) and is nondegenerate (`IsNondegenerate`: the time-one map $\Psi(1)$ of the fundamental solution of $\dot\Psi = J_0 S \Psi$, $\Psi(0) = \mathbb{1}$, has no eigenvalue $1$).
--
--   **Role.** Supplies a family of explicit nondegenerate asymptotic operators, for instance as end-points or reference operators in index computations for Cauchy-Riemann type operators on the cylinder.
-- source:
--   Setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry (arXiv:1011.1690), Ch. 4

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For `c ∈ (0, 2π)`, the constant loop `t ↦ c • 1` of `2m × 2m` matrices is a symmetric loop and
is nondegenerate. -/
theorem isNondegenerate_const_smul_one (m : ℕ) (c : ℝ) (hc : c ∈ Ioo 0 (2 * π)) :
    IsSymLoop (fun _ : ℝ => c • (1 : Mat m)) ∧ IsNondegenerate (fun _ : ℝ => c • (1 : Mat m)) := by
  sorry

end FiniteEnergyPlane
