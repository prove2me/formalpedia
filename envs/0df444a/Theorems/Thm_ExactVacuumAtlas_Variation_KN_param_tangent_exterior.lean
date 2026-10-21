-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_KN_param_tangent_exterior
-- name    : ExactVacuumAtlas.Variation.KN.param_tangent_exterior
-- status  : Open
-- author  : @He Wang
-- created : 2026-10-21T01:51:16.806246+00:00
-- url     : https://prove2.me/theorems/c0bc61e6-9405-4f61-a967-503fe0237d8e
-- title:
--   KN parameter tangents solve the linearised equations on the exterior
-- statement:
--   KN parameter tangents solve the linearised equations on the exterior
--
--   For all real M, a, Q, m, α, q with M > 0 and x ∈ domKN M a Q: with h = paramTangent (ε ↦ gKN (M + εm) (a + εα) (Q + εq)) and f = paramTangent (ε ↦ faradayKN (a + εα) (Q + εq)) (componentwise ε-derivative at 0), the linearised residuals LE, LJ, LH of the KN background vanish at x.
--
--   **Scope.** The tangent is represented by the genuine paramTangent of the family; no separate explicit closed form of all tangent components is claimed. No derivative of rPlus is taken and nothing is divided by a or Q.
--
--   **中文摘要** KN 三参数切向（用真实 paramTangent 表示）在外域满足线性化方程。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/KN.lean#L86-L95; SHA-256 dba90888f19cb0f545a02c26c83f1e3649e4fb4f71e4bbf5f3c1b37ebc3fa51f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_KN
import Definitions.Def_Atlas_Kerr_Frame
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_KerrBL_CoordGeometry
import Definitions.Def_KerrBL_Kerr_Metric
open Real
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.KN

theorem ExactVacuumAtlas.Variation.KN.param_tangent_exterior (M a Q m α q : ℝ) (hM : 0 < M) {x : Pt 4} (hx : x ∈ domKN M a Q) :
    (∀ i j, linEinstein (gKN M a Q) (giKN M a Q) (faradayKN a Q)
      (paramTangent fun ε => gKN (M + ε * m) (a + ε * α) (Q + ε * q))
      (paramTangent fun ε => faradayKN (a + ε * α) (Q + ε * q)) i j x = 0) ∧
    (∀ j, linMaxwell (gKN M a Q) (giKN M a Q) (faradayKN a Q)
      (paramTangent fun ε => gKN (M + ε * m) (a + ε * α) (Q + ε * q))
      (paramTangent fun ε => faradayKN (a + ε * α) (Q + ε * q)) j x = 0) ∧
    (∀ i j k, linFaraday (paramTangent fun ε => faradayKN (a + ε * α) (Q + ε * q)) i j k x = 0) := by sorry
