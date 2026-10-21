-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linMaxwell_eq_zero_of_onShell
-- name    : ExactVacuumAtlas.Variation.linMaxwell_eq_zero_of_onShell
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:49.074671+00:00
-- url     : https://prove2.me/theorems/efe139d1-5da3-45ed-bd4d-744f82cb927c
-- title:
--   On-shell corollary for LJ
-- statement:
--   On-shell corollary for LJ
--
--   For a FamilyData family whose J vanishes on all of W: LJ = 0 at every x with (0, x) ∈ W.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 解族的 LJ = 0（推论）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L275-L282; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.linMaxwell_eq_zero_of_onShell {g ginv : ℝ → Metric n} {F : ℝ → TwoForm n} {W : Set (ℝ × Pt n)}
    {h : Metric n} {f : TwoForm n} (hfam : FamilyData g ginv F W) (ht : IsTangent g F W h f)
    (hJ : ∀ p ∈ W, ∀ b, maxwellDiv (g p.1) (ginv p.1) (F p.1) b p.2 = 0)
    {x : Pt n} (hx : ((0 : ℝ), x) ∈ W) (b : Fin n) :
    linMaxwell (g 0) (ginv 0) (F 0) h f b x = 0 := by sorry
