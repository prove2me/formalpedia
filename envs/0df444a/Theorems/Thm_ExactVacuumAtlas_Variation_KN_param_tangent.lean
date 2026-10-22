-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_KN_param_tangent
-- name    : ExactVacuumAtlas.Variation.KN.param_tangent
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:59.617456+00:00
-- url     : https://prove2.me/theorems/4303e716-668d-4404-a3ee-7e95fc7b5fe6
-- title:
--   KN parameter tangents on the regular set
-- statement:
--   KN parameter tangents on the regular set
--
--   As param_tangent_exterior, on domReg M a Q = {Σ ≠ 0, Δ ≠ 0, sin θ ≠ 0} for every real M, a, Q, m, α, q.
--
--   **Scope.** Every real parameter; domReg includes both signs of Δ.
--
--   **中文摘要** KN 参数切向在正则集 domReg 上（任意实参数）满足线性化方程。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/KN.lean#L62-L84; SHA-256 dba90888f19cb0f545a02c26c83f1e3649e4fb4f71e4bbf5f3c1b37ebc3fa51f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.KN.param_tangent (M a Q m α q : ℝ) {x : Pt 4} (hx : x ∈ domReg M a Q) :
    (∀ i j, linEinstein (gKN M a Q) (giKN M a Q) (faradayKN a Q)
      (paramTangent fun ε => gKN (M + ε * m) (a + ε * α) (Q + ε * q))
      (paramTangent fun ε => faradayKN (a + ε * α) (Q + ε * q)) i j x = 0) ∧
    (∀ j, linMaxwell (gKN M a Q) (giKN M a Q) (faradayKN a Q)
      (paramTangent fun ε => gKN (M + ε * m) (a + ε * α) (Q + ε * q))
      (paramTangent fun ε => faradayKN (a + ε * α) (Q + ε * q)) j x = 0) ∧
    (∀ i j k, linFaraday (paramTangent fun ε => faradayKN (a + ε * α) (Q + ε * q)) i j k x = 0) := by sorry
