-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_sigma_coeff_KN
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.sigma_coeff_KN
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:28.079989+00:00
-- url     : https://prove2.me/theorems/8d500b62-79f8-4fbd-89aa-3b7ea2f9d2df
-- title:
--   σ-coefficient of NP Bianchi (b) at KN = −F₋/q̄³
-- statement:
--   σ-coefficient of NP Bianchi (b) at KN = −F₋/q̄³
--
--   For p : SubextremalKN on domReg: 3Ψ₂ + ½(R(l,n) + R(m,m̄)) = −F₋/q̄³ with III's frozen Fminus.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Bianchi (b) 的 σ 系数 = −F₋/q̄³。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPSourceMap.lean#L63-L75; SHA-256 63ae984e255ebf6522205e943eb4d4d068b8ef364d12ac684374493304591cf7. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Real Complex
open scoped ComplexConjugate ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN faradayKN domReg)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable (p : Hintz2026.SubextremalKN) {x : Pt 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.sigma_coeff_KN (hx : x ∈ domReg p.M p.a p.Q) :
    3 * psi2 (gKN p.M p.a p.Q) (giKN p.M p.a p.Q) (knE p.M p.a p.Q) x
      + (ricF (gKN p.M p.a p.Q) (giKN p.M p.a p.Q) (knE p.M p.a p.Q) 0 1 x
        + ricF (gKN p.M p.a p.Q) (giKN p.M p.a p.Q) (knE p.M p.a p.Q) 2 3 x) / 2
      = -Hintz2026.Fminus p (toRT x) / qbarK p.a x ^ 3 := by sorry
