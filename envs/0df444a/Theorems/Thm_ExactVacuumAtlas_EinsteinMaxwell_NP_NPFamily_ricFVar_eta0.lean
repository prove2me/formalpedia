-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_NPFamily_ricFVar_eta0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.NPFamily.ricFVar_eta0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:08.978203+00:00
-- url     : https://prove2.me/theorems/8376716f-d5cb-4a8c-8b50-dbba550e121d
-- title:
--   First variation of the η_{AK} = 0 frame Ricci components
-- statement:
--   First variation of the η_{AK} = 0 frame Ricci components
--
--   Genuine first variation of Ric(e_A, e_K) for η_{AK} = 0, written in source form (stress variation + L_E + frame-variation terms).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** η_{AK}=0 的标架 Ricci 分量的真实一阶变分（源形式）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Src.lean#L57-L73; SHA-256 cf20b5e9593790bd47fc233d856a0cde0f481acea030139ae7534ec0078491f0. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Cplx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinKN
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinMx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Src
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Complex Filter Topology
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.Variation
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del gKN giKN domReg domKN faradayKN)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {g gi : ℝ → Metric 4} {F : ℝ → TwoForm 4} {E Θ : ℝ → Fin 4 → Fin 4 → Pt 4 → ℂ} {W : Set (ℝ × Pt 4)}
  {h : Metric 4} {f : TwoForm 4} {B : Fin 4 → Fin 4 → Pt 4 → ℂ}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.NPFamily.ricFVar_eta0 (hF : NPFamily g gi F E Θ W) (ht : NPTangent g F E W h f B) {x : Pt 4}
    (hx : ((0 : ℝ), x) ∈ W) {A K : Fin 4} (h0 : etaNull A K = 0) :
    ricFVar (g 0) (gi 0) h (E 0) B A K x
      = 2 * ∑ C, ∑ D, (FfrFVar (F 0) f (E 0) B A C x * etaNull C D * FfrF (F 0) (E 0) K D x
          + FfrF (F 0) (E 0) A C x * etaNull C D * FfrFVar (F 0) f (E 0) B K D x)
        + (ccontr (linEinstein (g 0) (gi 0) (F 0) h f) x (fvec (E 0) A x) (fvec (E 0) K x)
          + ccontr (einsteinMaxwell (g 0) (gi 0) (F 0)) x (fvec B A x) (fvec (E 0) K x)
          + ccontr (einsteinMaxwell (g 0) (gi 0) (F 0)) x (fvec (E 0) A x) (fvec B K x)) := by sorry
