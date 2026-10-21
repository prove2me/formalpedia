-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linFaraday_eq_zero_of_onShell
-- name    : ExactVacuumAtlas.Variation.linFaraday_eq_zero_of_onShell
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:23.682465+00:00
-- url     : https://prove2.me/theorems/6f25a647-4176-4dd7-a8b4-fc7d47e0f74c
-- title:
--   On-shell corollary for LH
-- statement:
--   On-shell corollary for LH
--
--   For a FamilyData family whose H vanishes on all of W: LH(f) = 0 at every x with (0, x) ∈ W.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 解族的 LH = 0（推论，不是一般桥）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L284-L291; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.linFaraday_eq_zero_of_onShell {g ginv : ℝ → Metric n} {F : ℝ → TwoForm n} {W : Set (ℝ × Pt n)}
    {h : Metric n} {f : TwoForm n} (hfam : FamilyData g ginv F W) (ht : IsTangent g F W h f)
    (hH : ∀ p ∈ W, ∀ a b c, faradayCyclic (F p.1) a b c p.2 = 0)
    {x : Pt n} (hx : ((0 : ℝ), x) ∈ W) (a b c : Fin n) :
    linFaraday f a b c x = 0 := by sorry
