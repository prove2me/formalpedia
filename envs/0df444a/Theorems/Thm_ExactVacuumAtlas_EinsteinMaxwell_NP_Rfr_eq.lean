-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_Rfr_eq
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.Rfr_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:58.045638+00:00
-- url     : https://prove2.me/theorems/d343d7b5-f212-48de-9533-570fb483efd7
-- title:
--   Frame curvature = frame components of the curvature of ω
-- statement:
--   Frame curvature = frame components of the curvature of ω
--
--   For FrameData: Rfr equals the frame components of the coordinate curvature of ω (the −cΩ term is what the derivatives of the frame coefficients produce).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 标架曲率等于 ω 曲率的标架分量。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameConn.lean#L338-L353; SHA-256 2a10cd770a38610029f7546d603b6e7d5f8af619e7c052fbab673dadeffc4f32. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.Rfr_eq (hF : FrameData g gi E Θ U) {x : Pt n} (hx : x ∈ U) (A B : Fin n) :
    Rfr g gi E Θ A B x = ∑ μ, ∑ ν, (E A μ x * E B ν x) • Fom g gi E Θ μ ν x := by sorry
