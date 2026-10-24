-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_rz_inv
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.rz_inv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:02.16058+00:00
-- url     : https://prove2.me/theorems/b8e28387-1f24-4274-b98f-633d00a2f908
-- title:
--   Realisation family: true inverse metric
-- statement:
--   Realisation family: true inverse metric
--
--   On rzW: metricMatrix(rzGI) · metricMatrix(rzG) = 1 for every slice.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 实现族的逆度规为真逆。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Realize.lean#L324-L340; SHA-256 a3ba6bed8a3f274a79c27da921d2b891c251411ce219cec944034d43e884039b. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable {U : Set (Pt 4)} {g0 gi0 : Metric 4} {F0 f : TwoForm 4} {E0 Θ0 B : Fin 4 → Fin 4 → Pt 4 → ℂ}
  {h : Metric 4}
variable (hN : NullFrameData g0 gi0 E0 Θ0 U) (ht : RealFrameTangent g0 E0 U h f B)
include hN ht

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.rz_inv {p : ℝ × Pt 4} (hp : p ∈ rzW U E0 B) (hR0 : RealPattern E0 U) :
    metricMatrix (rzGI U gi0 E0 B p.1) p.2 * metricMatrix (rzG U g0 E0 Θ0 B p.1) p.2 = 1 := by sorry
