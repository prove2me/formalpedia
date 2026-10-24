-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_pdMC_gramM
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.pdMC_gramM
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:08.072786+00:00
-- url     : https://prove2.me/theorems/0548525d-97d8-4c8b-8be5-3a32b6190d77
-- title:
--   Metric compatibility (matrix form)
-- statement:
--   Metric compatibility (matrix form)
--
--   For FrameData: ∂_μ G = ω_μᵀ G + G ω_μ for the Gram matrix G = Eᵀ g E.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 度规相容性（矩阵形式）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameConn.lean#L411-L425; SHA-256 2a10cd770a38610029f7546d603b6e7d5f8af619e7c052fbab673dadeffc4f32. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.pdMC_gramM (hF : FrameData g gi E Θ U) {x : Pt n} (hx : x ∈ U) (μ : Fin n) :
    pdMC μ (gramM g E) x = (omegaC g gi E Θ μ x)ᵀ * gramM g E x + gramM g E x * omegaC g gi E Θ μ x := by sorry
