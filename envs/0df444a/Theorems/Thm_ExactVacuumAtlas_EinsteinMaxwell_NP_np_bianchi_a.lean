-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_bianchi_a
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_bianchi_a
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:28.587342+00:00
-- url     : https://prove2.me/theorems/c63a6718-44cb-4c8f-9300-3950b25eb46b
-- title:
--   NP Bianchi identity (a) with Ricci sources, any null frame
-- statement:
--   NP Bianchi identity (a) with Ricci sources, any null frame
--
--   For any 4D metric data and any complex null frame with NullFrameData g gi E Θ U (no field equation): at x ∈ U, −D Ψ₁ + δ̄ Ψ₀ + ½ D R(l,m) − ½ δ R(l,l) = −2Ψ₁ε − 4Ψ₁ρ + 4Ψ₀α − Ψ₀π + 3Ψ₂κ + (Ricci source terms), with D = fdir E 0, δ = fdir E 2, δ̄ = fdir E 3 and the exact source terms printed in the statement (R(·,·) = ricF; B-suffixed coefficients are the m ↔ m̄ swapped components). It is the geometric source of III's res1a.
--
--   **Scope.** General null frame on an open set (NullFrameData); no field equation.
--
--   **中文摘要** 任意零标架下的 NP Bianchi 恒等式 (a)，保留全部 Ricci 源项；不假设场方程；为 III 的 res1a 的几何来源。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPBianchiNP.lean#L412-L447; SHA-256 ea0382ebea92c4638a3d050ceb9e7891f3c8fee12cfa1baecd44232265e2ddb3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPBianchi
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPMaxwell
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPRicci
import Definitions.Def_Atlas_EinsteinMaxwell_NP_NPScalars
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Riemann
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff Matrix
open Complex
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
set_option linter.unusedSimpArgs false
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_bianchi_a (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) :
    (-1) * fdir E 0 (psi1 g gi E) x +
        (1) * fdir E 3 (psi0 g gi E) x +
        (1/2) * fdir E 0 (ricF g gi E 0 2) x +
        (-1/2) * fdir E 2 (ricF g gi E 0 0) x
      = (-2) * psi1 g gi E x * npEps g gi E Θ x +
        (-4) * psi1 g gi E x * npRho g gi E Θ x +
        (4) * psi0 g gi E x * npAlpha g gi E Θ x +
        (-1) * psi0 g gi E x * npPi g gi E Θ x +
        (3) * psi2 g gi E x * npKappa g gi E Θ x +
        (-1) * npAlphaB g gi E Θ x * ricF g gi E 0 0 x +
        (-1) * npBeta g gi E Θ x * ricF g gi E 0 0 x +
        (1) * npEps g gi E Θ x * ricF g gi E 0 2 x +
        (-1/2) * npKappa g gi E Θ x * ricF g gi E 0 1 x +
        (-1/2) * npKappa g gi E Θ x * ricF g gi E 2 3 x +
        (-1/2) * npKappaB g gi E Θ x * ricF g gi E 2 2 x +
        (1/2) * npPiB g gi E Θ x * ricF g gi E 0 0 x +
        (1) * npRhoB g gi E Θ x * ricF g gi E 0 2 x +
        (1) * ricF g gi E 0 3 x * npSigma g gi E Θ x := by sorry
