-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_hasDerivAt_ccontr4_fam
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_ccontr4_fam
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:55.238144+00:00
-- url     : https://prove2.me/theorems/ab961902-5492-42dd-9763-964be66e6cd1
-- title:
--   Product rule for the 4-fold contraction of families
-- statement:
--   Product rule for the 4-fold contraction of families
--
--   ε-derivative of the complex-multilinear contraction of a real 4-tensor family with four vector families.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 四重缩并族的乘积法则。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Family.lean#L84-L102; SHA-256 f001c2ffe97be7cb54821fc20999d8e3421a6ca079fc1d83110f9ad9b80590e4. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Family
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.hasDerivAt_ccontr4_fam {T : ℝ → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Pt 4 → ℝ}
    {T' : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Pt 4 → ℝ}
    {u v w z : ℝ → Fin 4 → ℂ} {u' v' w' z' : Fin 4 → ℂ} {x : Pt 4}
    (hT : ∀ a b c d, HasDerivAt (fun ε => T ε a b c d x) (T' a b c d x) 0)
    (hu : ∀ i, HasDerivAt (fun ε => u ε i) (u' i) 0) (hv : ∀ i, HasDerivAt (fun ε => v ε i) (v' i) 0)
    (hw : ∀ i, HasDerivAt (fun ε => w ε i) (w' i) 0) (hz : ∀ i, HasDerivAt (fun ε => z ε i) (z' i) 0) :
    HasDerivAt (fun ε => ccontr4 (T ε) x (u ε) (v ε) (w ε) (z ε))
      (ccontr4 T' x (u 0) (v 0) (w 0) (z 0) + ccontr4 (T 0) x u' (v 0) (w 0) (z 0)
        + ccontr4 (T 0) x (u 0) v' (w 0) (z 0) + ccontr4 (T 0) x (u 0) (v 0) w' (z 0)
        + ccontr4 (T 0) x (u 0) (v 0) (w 0) z') 0 := by sorry
