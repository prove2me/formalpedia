-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_contDiffOn_christoffel_joint
-- name    : ExactVacuumAtlas.Variation.contDiffOn_christoffel_joint
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:34.600169+00:00
-- url     : https://prove2.me/theorems/437149fd-109d-434a-bed0-5eba7a417bdc
-- title:
--   Joint C^∞ of the Christoffel symbols
-- statement:
--   Joint C^∞ of the Christoffel symbols
--
--   If (ε, y) ↦ g_ε(y), ginv_ε(y) are jointly C^∞ on open W, so is (ε, y) ↦ Γ^a_{bc}(g_ε, ginv_ε)(y).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Christoffel 符号的联合 C^∞。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L32-L42; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.contDiffOn_christoffel_joint {g ginv : ℝ → Metric n} {W : Set (ℝ × Pt n)} (hW : IsOpen W)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × Pt n => g p.1 i j p.2) W)
    (hgi : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × Pt n => ginv p.1 i j p.2) W) (a b c : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Pt n => christoffel (g p.1) (ginv p.1) a b c p.2) W := by sorry
