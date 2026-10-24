-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_np_bianchi_b_neg
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.np_bianchi_b_neg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:15.676574+00:00
-- url     : https://prove2.me/theorems/004eaa0f-794a-42cb-b506-a141ec94de22
-- title:
--   Negative NP Bianchi identity (GHP prime of (b))
-- statement:
--   Negative NP Bianchi identity (GHP prime of (b))
--
--   Component (n,m̄; l,n,m̄) with Ricci sources. Source of III's res1bN.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 负支 Bianchi（(b) 的 GHP 撇）；res1bN 的来源。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPBianchiNP.lean#L523-L558; SHA-256 ea0382ebea92c4638a3d050ceb9e7891f3c8fee12cfa1baecd44232265e2ddb3. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.np_bianchi_b_neg (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) :
    (1) * fdir E 0 (psi4 g gi E) x +
        (-1) * fdir E 3 (psi3 g gi E) x +
        (1/2) * fdir E 1 (ricF g gi E 3 3) x +
        (-1/2) * fdir E 3 (ricF g gi E 1 3) x
      = (2) * psi3 g gi E x * npAlpha g gi E Θ x +
        (4) * psi3 g gi E x * npPi g gi E Θ x +
        (-3) * psi2 g gi E x * npLambda g gi E Θ x +
        (-4) * psi4 g gi E x * npEps g gi E Θ x +
        (1) * psi4 g gi E x * npRho g gi E Θ x +
        (1) * npAlpha g gi E Θ x * ricF g gi E 1 3 x +
        (-1) * npGamma g gi E Θ x * ricF g gi E 3 3 x +
        (1) * npGammaB g gi E Θ x * ricF g gi E 3 3 x +
        (-1/2) * npLambda g gi E Θ x * ricF g gi E 0 1 x +
        (-1/2) * npLambda g gi E Θ x * ricF g gi E 2 3 x +
        (-1/2) * npMuB g gi E Θ x * ricF g gi E 3 3 x +
        (1) * npNu g gi E Θ x * ricF g gi E 0 3 x +
        (1/2) * ricF g gi E 1 1 x * npSigmaB g gi E Θ x +
        (-1) * ricF g gi E 1 3 x * npTauB g gi E Θ x := by sorry
