-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_frame_bianchi
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.frame_bianchi
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:59.646995+00:00
-- url     : https://prove2.me/theorems/dfa45d72-9652-42b4-8959-1ef36a16fc09
-- title:
--   Second Bianchi identity in a general frame
-- statement:
--   Second Bianchi identity in a general frame
--
--   Gauge form of the second Bianchi identity for the frame curvature, with the −c R term.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般标架下第二 Bianchi 恒等式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/Bianchi.lean#L154-L224; SHA-256 7a3a9c6ef7ae1ad57f306317ff9e948f3f7ad12cb60d92e1b8e75baaccf75870. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {n : ℕ}
variable {g gi : Metric n} {E Θ : Fin n → Fin n → Pt n → ℂ} {U : Set (Pt n)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.frame_bianchi (hF : FrameData g gi E Θ U) {x : Pt n} (hx : x ∈ U) (C A B : Fin n) :
    bianchiX g gi E Θ C A B x + bianchiX g gi E Θ A B C x + bianchiX g gi E Θ B C A x = 0 := by sorry
