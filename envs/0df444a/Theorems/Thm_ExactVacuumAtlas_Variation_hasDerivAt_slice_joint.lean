-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_slice_joint
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_slice_joint
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:46.220988+00:00
-- url     : https://prove2.me/theorems/57cd70d1-e7a9-441e-a503-2521d17e9198
-- title:
--   Coordinate slice of a jointly differentiable map
-- statement:
--   Coordinate slice of a jointly differentiable map
--
--   IV calculus helper: if φ : ℝ × Pt n → ℝ is differentiable at p, then, with the first coordinate p.1 held fixed, the coordinate slice u ↦ φ(p.1, update p.2 i u) has derivative fderiv ℝ φ p (0, Pi.single i 1) at u = p.2 i. This is differentiation in the i-th Pt n coordinate slot, not in the family parameter ε.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** IV 联合可微映射的坐标切片导数：固定参数 p.1，只改变 p.2 的第 i 个坐标；导数方向是 (0, Pi.single i 1)，不是对 ε 求导。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/Variation/Joint.lean#L32-L42; SHA-256 4b63c47f27fd80bedab505cf38c5c13014839c88f3159852417904171ca49a55. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.hasDerivAt_slice_joint {φ : ℝ × Pt n → ℝ} {p : ℝ × Pt n} (hd : DifferentiableAt ℝ φ p)
    (i : Fin n) :
    HasDerivAt (fun u : ℝ => φ (p.1, Function.update p.2 i u))
      (fderiv ℝ φ p ((0 : ℝ), (Pi.single i 1 : Pt n))) (p.2 i) := by sorry
