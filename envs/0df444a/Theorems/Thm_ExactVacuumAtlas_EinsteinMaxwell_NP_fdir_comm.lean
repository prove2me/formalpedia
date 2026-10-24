-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_fdir_comm
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_comm
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:09.278391+00:00
-- url     : https://prove2.me/theorems/b77a4ba9-e89e-41e8-b0fb-6a289f20b353
-- title:
--   Commutator of frame derivatives
-- statement:
--   Commutator of frame derivatives
--
--   For C^∞ f: [D_A, D_B] f = Σ_C c^C_{AB} D_C f.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 标架导数对易子。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameConn.lean#L213-L231; SHA-256 2a10cd770a38610029f7546d603b6e7d5f8af619e7c052fbab673dadeffc4f32. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_CCalc
import Definitions.Def_Atlas_EinsteinMaxwell_NP_FrameConn
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {n : ℕ}
variable {g gi : Metric n} {E Θ : Fin n → Fin n → Pt n → ℂ} {U : Set (Pt n)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_comm (hF : FrameData g gi E Θ U) {x : Pt n} (hx : x ∈ U) (A B : Fin n) {f : Pt n → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) :
    fdir E A (fdir E B f) x - fdir E B (fdir E A f) x = ∑ C, cfr E Θ C A B x * fdir E C f x := by sorry
