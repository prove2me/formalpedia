-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_cpdC_mode_phi
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.cpdC_mode_phi
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:02.209624+00:00
-- url     : https://prove2.me/theorems/e4bf3817-5bb2-4bee-b7c9-ebbdaeb8718c
-- title:
--   φ-derivative of a mode field
-- statement:
--   φ-derivative of a mode field
--
--   cpdC 3 (modeField ω m u) x = i m · modeField ω m u x (unconditional).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 模式场的 φ 导数 = i m ×。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/ModeOperators.lean#L99-L110; SHA-256 c032a93690f8cd1e86823b77830e6194e4b5993b195ecd433c60982fee8e3afe. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.cpdC_mode_phi : cpdC 3 (modeField om mm u) x = Complex.I * mm * modeField om mm u x := by sorry
