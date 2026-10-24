-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_ricF_eq_source
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.ricF_eq_source
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:20:04.359614+00:00
-- url     : https://prove2.me/theorems/1f0ed1e6-31c1-48db-9d81-687c19ed215d
-- title:
--   Frame Ricci components in source form
-- statement:
--   Frame Ricci components in source form
--
--   For any null frame and any F (off shell): Ric(e_A, e_B) = 2 S(e_A, e_B) + E(e_A, e_B) − ½ η_{AB} tr E, E = IV's einsteinMaxwell residual.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 标架 Ricci 分量的源形式 2S+E−½η trE（离壳）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/NPSourceMap.lean#L26-L43; SHA-256 63ae984e255ebf6522205e943eb4d4d068b8ef364d12ac684374493304591cf7. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.ricF_eq_source {g gi : Metric 4} {E Θ : Fin 4 → Fin 4 → Pt 4 → ℂ} {U : Set (Pt 4)}
    (hN : NullFrameData g gi E Θ U) {x : Pt 4} (hx : x ∈ U) (F : TwoForm 4) (A B : Fin 4) :
    ricF g gi E A B x = 2 * ccontr (emStress g gi F) x (fvec E A x) (fvec E B x)
      + ccontr (einsteinMaxwell g gi F) x (fvec E A x) (fvec E B x)
      - etaNull A B * ((∑ c, ∑ d, gi c d x * einsteinMaxwell g gi F c d x : ℝ) : ℂ) / 2 := by sorry
