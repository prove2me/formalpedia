-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_raise2_of
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_raise2_of
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:44.898487+00:00
-- url     : https://prove2.me/theorems/8c25ce43-7017-46e5-b708-74ac184dd0f4
-- title:
--   Pointwise derivative of F^{ab}
-- statement:
--   Pointwise derivative of F^{ab}
--
--   Given the ε-derivatives of ginv (invVar) and F at y, the derivative of raise2 at y is raise2Var.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 升指标场的导数。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L78-L86; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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
variable {g ginv : ℝ → Metric n} {F : ℝ → TwoForm n} {h : Metric n} {f : TwoForm n} {y : Pt n}

theorem ExactVacuumAtlas.Variation.hasDerivAt_raise2_of
    (hgi : ∀ i j, HasDerivAt (fun ε => ginv ε i j y) (invVar (ginv 0) h i j y) 0)
    (hF : ∀ i j, HasDerivAt (fun ε => F ε i j y) (f i j y) 0) (a b : Fin n) :
    HasDerivAt (fun ε => raise2 (ginv ε) (F ε) a b y) (raise2Var (ginv 0) h (F 0) f a b y) 0 := by sorry
