-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_mode_directions
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.mode_directions
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:22:08.792673+00:00
-- url     : https://prove2.me/theorems/21a2e595-4f79-4410-98aa-24c1d7ca20ae
-- title:
--   All four frame directions of a mode field
-- statement:
--   All four frame directions of a mode field
--
--   On III's exterior domKN: l, n, m, m̄ act on modeField ω m u as P · Dop, P(−Δ/2Σ) · DopDag, P/(√2ρ̄) · LopDag, P/(√2ρ̄*) · Lop at j = 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 模式场的四个标架方向导数。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/ModeOperators.lean#L244-L258; SHA-256 c032a93690f8cd1e86823b77830e6194e4b5993b195ecd433c60982fee8e3afe. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
variable (p : Hintz2026.SubextremalKN) (om mm : ℝ) (u : (Fin 2 → ℝ) → ℂ) (x : Pt 4)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.mode_directions (hx : x ∈ domKN p.M p.a p.Q) :
    cdir (knFrame p.M p.a p.Q x 0) (modeField om mm u) x =
        phaseP om mm x * Hintz2026.Dop p 0 om mm u (toRT x) ∧
      cdir (knFrame p.M p.a p.Q x 1) (modeField om mm u) x =
        phaseP om mm x * (-((Del p.M p.a p.Q (x 1) / (2 * Sig p.a (x 1) (x 2)) : ℝ) : ℂ)) *
          Hintz2026.DopDag p 0 om mm u (toRT x) ∧
      cdir (knFrame p.M p.a p.Q x 2) (modeField om mm u) x =
        phaseP om mm x / (((Real.sqrt 2 : ℝ) : ℂ) * Hintz2026.rhoBar p (toRT x)) *
          Hintz2026.LopDag p 0 om mm u (toRT x) ∧
      cdir (knFrame p.M p.a p.Q x 3) (modeField om mm u) x =
        phaseP om mm x / (((Real.sqrt 2 : ℝ) : ℂ) * Hintz2026.rhoBarStar p (toRT x)) *
          Hintz2026.Lop p 0 om mm u (toRT x) := by sorry
