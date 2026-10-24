-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_NPFamily_hasDerivAt_weyl
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.NPFamily.hasDerivAt_weyl
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:02.286743+00:00
-- url     : https://prove2.me/theorems/4df9e836-6e5c-45af-a06f-12b45d5ccfc0
-- title:
--   Genuine first variation of the Weyl tensor
-- statement:
--   Genuine first variation of the Weyl tensor
--
--   For an NPFamily with tangent (h, f, B): ε ↦ weyl (g ε) (gi ε) a b c d x has derivative weylVar (g 0) (gi 0) h a b c d x at 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Weyl 张量的真实一阶变分。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Var.lean#L145-L158; SHA-256 208236fc7bbbf59f60939aacdcc4f56b54f83656fb1b932f24ef4e179bf07389. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Bianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNComm
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNSpin
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNWeyl
import Definitions.Def_Atlas_EinsteinMaxwell_NP_ModeOperators
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPBianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Complex Filter Topology
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.Variation
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {g gi : ℝ → Metric 4} {F : ℝ → TwoForm 4} {E Θ : ℝ → Fin 4 → Fin 4 → Pt 4 → ℂ} {W : Set (ℝ × Pt 4)}
  {h : Metric 4} {f : TwoForm 4} {B : Fin 4 → Fin 4 → Pt 4 → ℂ}
variable (hF : NPFamily g gi F E Θ W) (ht : NPTangent g F E W h f B) {x : Pt 4} (hx : ((0 : ℝ), x) ∈ W)
include hF ht hx

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.NPFamily.hasDerivAt_weyl (a b c d : Fin 4) :
    HasDerivAt (fun ε => weyl (g ε) (gi ε) a b c d x) (weylVar (g 0) (gi 0) h a b c d x) 0 := by sorry
