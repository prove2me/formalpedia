-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_RN_b_tangent_maxwell_closed
-- name    : ExactVacuumAtlas.Variation.RN.b_tangent_maxwell_closed
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:06.618466+00:00
-- url     : https://prove2.me/theorems/147d46c5-a5a8-44af-9e54-6dbef8af4d63
-- title:
--   The RN b-direction has vanishing Maxwell and Faraday linearised residuals
-- statement:
--   The RN b-direction has vanishing Maxwell and Faraday linearised residuals
--
--   For all real M, Q and x ∈ domRN: LJ^b(gRN M (Q²), giRN M (Q²), faradayRN Q; tanB, 0)(x) = 0 for all b and LH_abc(0)(x) = 0.
--
--   **Scope.** Same direction as nonzero_theta.
--
--   **中文摘要** 同一方向的 Maxwell 与闭合线性残差为零（只有 Einstein 部分非零）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/RN.lean#L177-L187; SHA-256 7513cd6c91a5e550bb62e1cac2f2c8a8c17fa469087ba3c27bf9c1eab933f66f. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.RN.b_tangent_maxwell_closed (M Q : ℝ) {x : Pt 4} (hx : x ∈ domRN) :
    (∀ b, linMaxwell (gRN M (Q ^ 2)) (giRN M (Q ^ 2)) (faradayRN Q) tanB 0 b x = 0) ∧
    (∀ a b c, linFaraday (0 : TwoForm 4) a b c x = 0) := by sorry
