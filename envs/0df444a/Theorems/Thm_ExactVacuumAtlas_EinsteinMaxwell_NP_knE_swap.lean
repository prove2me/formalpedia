-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_knE_swap
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.knE_swap
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:23.109403+00:00
-- url     : https://prove2.me/theorems/5b24c03b-8a90-462a-80af-d8c63d069288
-- title:
--   Reality pattern of the KN frame
-- statement:
--   Reality pattern of the KN frame
--
--   knE M a Q (swap23 A) μ x = conj (knE M a Q A μ x): l, n real and m̄ = conj m.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 标架的实性模式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNSpin.lean#L113-L121; SHA-256 296633d32af53ca44cec2982a7dc3dc99a1cb3e71bd617f51817c313623dfb02. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameNull
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNSpin
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open Real Complex
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN faradayKN domReg)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.knE_swap (M a Q : ℝ) (A μ : Fin 4) (x : Pt 4) :
    knE M a Q (swap23 A) μ x = conj (knE M a Q A μ x) := by sorry
