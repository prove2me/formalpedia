-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_RN_param_tangent
-- name    : ExactVacuumAtlas.Variation.RN.param_tangent
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:57.366519+00:00
-- url     : https://prove2.me/theorems/4174d806-4a97-4065-8715-c17ee738de89
-- title:
--   RN mass/charge tangents solve the linearised equations
-- statement:
--   RN mass/charge tangents solve the linearised equations
--
--   For all real M, Q, m, q and x ∈ domRN, with background (gRN M (Q²), giRN M (Q²), faradayRN Q) and the explicit tangent h = tanRN Q m q (only h_vv = 2m/r − 2Qq/r²), f = tanFRN q (f_vr = −q/r², f_rv = q/r²): LE_ab = 0 for all a, b, LJ^b = 0 for all b, LH_abc = 0 for all a, b, c.
--
--   **Scope.** The tangent is the true ε-derivative of the RN family (M + εm, Q + εq) (familyData_param, isTangent_param); zero follows from the off-shell bridge applied to a family of certificates. First-order statement only.
--
--   **中文摘要** RN 质量/电荷参数切向（显式 h_vv=2m/r−2Qq/r²，f_rv=q/r²）满足线性化方程（LE=LJ=LH=0）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/RN.lean#L133-L152; SHA-256 7513cd6c91a5e550bb62e1cac2f2c8a8c17fa469087ba3c27bf9c1eab933f66f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Frame
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_RN
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.RN

theorem ExactVacuumAtlas.Variation.RN.param_tangent (M Q m q : ℝ) {x : Pt 4} (hx : x ∈ domRN) :
    (∀ a b, linEinstein (gRN M (Q ^ 2)) (giRN M (Q ^ 2)) (faradayRN Q) (tanRN Q m q) (tanFRN q) a b x = 0) ∧
    (∀ b, linMaxwell (gRN M (Q ^ 2)) (giRN M (Q ^ 2)) (faradayRN Q) (tanRN Q m q) (tanFRN q) b x = 0) ∧
    (∀ a b c, linFaraday (tanFRN q) a b c x = 0) := by sorry
