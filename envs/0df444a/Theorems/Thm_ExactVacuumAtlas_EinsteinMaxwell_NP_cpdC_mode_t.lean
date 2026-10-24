-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_cpdC_mode_t
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.cpdC_mode_t
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:21:54.292869+00:00
-- url     : https://prove2.me/theorems/900652fc-cc18-4723-971d-c2d46d2fa3c9
-- title:
--   t-derivative of a mode field
-- statement:
--   t-derivative of a mode field
--
--   cpdC 0 (modeField ω m u) x = −i ω · modeField ω m u x (unconditional).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 模式场的 t 导数 = −iω ×。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/ModeOperators.lean#L86-L97; SHA-256 c032a93690f8cd1e86823b77830e6194e4b5993b195ecd433c60982fee8e3afe. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_EinsteinMaxwell_NP_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFaraday
import Definitions.Def_Atlas_EinsteinMaxwell_NP_KNFrame
import Definitions.Def_Atlas_EinsteinMaxwell_NP_ModeOperators
import Definitions.Def_Atlas_Kerr_InAtoms
import Definitions.Def_Hintz2026_Core
import Definitions.Def_Hintz2026_Domain
import Definitions.Def_Hintz2026_System1
import Definitions.Def_Hintz2026_System4
open Real
open scoped ComplexConjugate ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del domReg domKN)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable (om mm : ℝ) (u : (Fin 2 → ℝ) → ℂ) (x : Pt 4)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.cpdC_mode_t : cpdC 0 (modeField om mm u) x = -(Complex.I * om) * modeField om mm u x := by sorry
