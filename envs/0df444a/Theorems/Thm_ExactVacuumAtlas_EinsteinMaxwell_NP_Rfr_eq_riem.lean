-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_Rfr_eq_riem
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.Rfr_eq_riem
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:43.522366+00:00
-- url     : https://prove2.me/theorems/4feb6594-0e59-4749-867d-d45d74189600
-- title:
--   Frame curvature equals the frame components of the coordinate Riemann tensor
-- statement:
--   Frame curvature equals the frame components of the coordinate Riemann tensor
--
--   For any dimension n, any metric data and any complex frame/coframe pair satisfying FrameData g gi E Θ U (open U, C^∞ frame and dual, duality, MetricData): at x ∈ U, (Rfr A B)^I_J = Σ_{μνρσ} e_A^μ e_B^ν θ^I_ρ R^ρ_{σμν} e_J^σ, where Rfr is D_A Ω_B − D_B Ω_A + [Ω_A, Ω_B] − Σ_C c^C_{AB} Ω_C (including the −cΩ term) and R = riem g gi = II's curv(connMat(christoffel)).
--
--   **Scope.** General: total dimension n, FrameData hypotheses only (no field equation).
--
--   **中文摘要** 一般复标架下，标架曲率（含 −cΩ 项）等于坐标 Riemann 张量 riem 的标架分量；不用任何场方程。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/FrameConn.lean#L355-L364; SHA-256 2a10cd770a38610029f7546d603b6e7d5f8af619e7c052fbab673dadeffc4f32. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.Rfr_eq_riem (hF : FrameData g gi E Θ U) {x : Pt n} (hx : x ∈ U) (A B I J : Fin n) :
    Rfr g gi E Θ A B x I J = ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
      E A μ x * E B ν x * Θ I ρ x * (riem g gi ρ σ μ ν x : ℂ) * E J σ x := by sorry
