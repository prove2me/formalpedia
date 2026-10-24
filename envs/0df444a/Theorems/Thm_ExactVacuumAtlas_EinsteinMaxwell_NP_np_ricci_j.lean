-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_ricci_j
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_ricci_j
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:12.144991+00:00
-- url     : https://prove2.me/theorems/7bc64a18-2cc1-499c-a5de-9c1900ba2681
-- title:
--   NP Ricci identity (4.2j)
-- statement:
--   NP Ricci identity (4.2j)
--
--   On the stated null-frame domain, write D_A = fdir E A, with frame indices (l, n, m, m̄) = (0, 1, 2, 3). Since λ = −omL 1 3 3 and ν = −omL 1 1 3, the printed identity is −D₁λ + D₃ν = λ(μ + μ_B + 3γ − γ_B) − ν(π − τ_B + β_B + 3α) + Ψ₄. The B-suffixed coefficients are the index-swapped quantities in the formal statement; numerical complex conjugacy is not an extra hypothesis. This is a geometric source identity used for III's res1cN.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** NP Ricci 恒等式 (4.2j)：按 λ=−omL 1 3 3、ν=−omL 1 1 3 的定义，左端是 −D₁λ+D₃ν；B 后缀沿用指标交换定义。它是 res1cN 使用的几何来源恒等式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPRicci.lean#L224-L237; SHA-256 ac60d8d4c03ef192711b765ff96839ab1c7b0d06979f363abf6f01f165ba36cf. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
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
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_ricci_j (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) :
    fdir E 1 (omL g gi E Θ 1 3 3) x - fdir E 3 (omL g gi E Θ 1 1 3) x
      = npLambda g gi E Θ x * (npMu g gi E Θ x + npMuB g gi E Θ x + 3 * npGamma g gi E Θ x - npGammaB g gi E Θ x)
        - npNu g gi E Θ x * (npPi g gi E Θ x - npTauB g gi E Θ x + npBetaB g gi E Θ x + 3 * npAlpha g gi E Θ x)
        + psi4 g gi E x := by sorry
