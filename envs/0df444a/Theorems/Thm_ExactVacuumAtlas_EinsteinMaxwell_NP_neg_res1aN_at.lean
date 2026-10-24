-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_neg_res1aN_at
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.neg_res1aN_at
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:23:28.026208+00:00
-- url     : https://prove2.me/theorems/95d89f1b-3ece-4eea-b076-1dda13bcdf5d
-- title:
--   III's res1aN from the negative Bianchi (a)
-- statement:
--   III's res1aN from the negative Bianchi (a)
--
--   Under KNCTan, CLinEM, cPhi2 = 0 and NegMode: res1aN = 0 (multiplier P/(√2 q q̄⁴)).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** res1aN=0（乘子 P/(√2 q q̄⁴)）。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Res.lean#L288-L319; SHA-256 428706d4df792e38c8711c2b24c8ab30316521cacd37941872e4003eb33e73a5. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03C3
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Cplx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinKN
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03LinMx
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Mode
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Res
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Src
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Tan
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Var
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
import Definitions.Def_Hintz2026_Chiral
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
variable (p : Hintz2026.SubextremalKN) {τ : CTan} {om mm : ℝ}
local notation "rb" => Hintz2026.rhoBar p
local notation "rbs" => Hintz2026.rhoBarStar p
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
variable (hτ : KNCTan p.M p.a p.Q (domKN p.M p.a p.Q) τ)
include hτ

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.neg_res1aN_at {G : Hintz2026.NegFields} (hm : NegMode p τ om mm G) (hL : CLinEM p.M p.a p.Q (domKN p.M p.a p.Q) τ)
    (hg : ∀ y ∈ domKN p.M p.a p.Q, cPhi2 p.M p.a p.Q τ y = 0) {x : Pt 4}
    (hx : x ∈ domKN p.M p.a p.Q) : Hintz2026.res1aN p om mm G (toRT x) = 0 := by sorry
