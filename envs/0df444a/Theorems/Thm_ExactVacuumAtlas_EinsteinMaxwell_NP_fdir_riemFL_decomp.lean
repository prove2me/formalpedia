-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_fdir_riemFL_decomp
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_riemFL_decomp
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:02.596315+00:00
-- url     : https://prove2.me/theorems/47bb8ada-7fae-4fc6-970f-de357b51a318
-- title:
--   Frame derivative of the Weyl decomposition
-- statement:
--   Frame derivative of the Weyl decomposition
--
--   For a null frame: D_C R_{IJAB} = D_C C_{IJAB} + (Ricci terms)/2 − D_C R · (η η terms)/6, as printed.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Weyl 分解的标架导数。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPBianchi.lean#L134-L167; SHA-256 ade6663af1b9909aa47b81f0232caab876069cc980f89d447023557ca64a1609. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.fdir_riemFL_decomp (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) (C I J A B : Fin 4) :
    fdir E C (riemFL g gi E Θ I J A B) x = fdir E C (weylF g gi E I J A B) x
      + (etaNull I A * fdir E C (ricF g gi E J B) x - etaNull I B * fdir E C (ricF g gi E J A) x
        - etaNull J A * fdir E C (ricF g gi E I B) x + etaNull J B * fdir E C (ricF g gi E I A) x) / 2
      - fdir E C (fun z => (ricciScalar g gi z : ℂ)) x
        * (etaNull I A * etaNull J B - etaNull I B * etaNull J A) / 6 := by sorry
