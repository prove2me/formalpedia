-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_Omega_compat_const
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.Omega_compat_const
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:53.182986+00:00
-- url     : https://prove2.me/theorems/69e8e7b6-dccf-4ebc-b305-0a6f92c92dff
-- title:
--   Connection with constant Gram matrix
-- statement:
--   Connection with constant Gram matrix
--
--   With a constant Gram matrix η on U: Ω_Aᵀ η + η Ω_A = 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 常 Gram 矩阵时 Ωᵀη+ηΩ=0。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameConn.lean#L433-L445; SHA-256 2a10cd770a38610029f7546d603b6e7d5f8af619e7c052fbab673dadeffc4f32. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.Omega_compat_const (hF : FrameData g gi E Θ U) {η : Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ z ∈ U, gramM g E z = η) {x : Pt n} (hx : x ∈ U) (A : Fin n) :
    (Omega g gi E Θ A x)ᵀ * η + η * Omega g gi E Θ A x = 0 := by sorry
