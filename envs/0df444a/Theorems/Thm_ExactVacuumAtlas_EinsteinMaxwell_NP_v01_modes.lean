-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_v01_modes
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.v01_modes
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:26:45.95403+00:00
-- url     : https://prove2.me/theorems/c767e073-138c-4f76-92cb-0b6c4d284890
-- title:
--   Single-mode frame derivatives are III's j = 0 operators
-- statement:
--   Single-mode frame derivatives are III's j = 0 operators
--
--   For p : SubextremalKN, real ω, m and an amplitude u : ℝ² → ℂ that is C^∞ on U p: the mode field modeField ω m u (x ↦ exp(−iωt + imφ) u(r, θ)) is C^∞ on domKN; at every x ∈ domKN its coordinate partials are genuine derivatives (HasDerivAt), toRT x ∈ U p, phaseP ≠ 0, and the four frame directions act as l ↦ P · Dop p 0, n ↦ P · (−Δ/(2Σ)) · DopDag p 0, m ↦ P/(√2 ρ̄) · LopDag p 0, m̄ ↦ P/(√2 ρ̄*) · Lop p 0, with III's original operators at j = 0 and P = phaseP ω m x.
--
--   **Scope.** p : Hintz2026.SubextremalKN — III's parameter structure: M > 0, Q ≠ 0, a² + Q² < M² (a = 0 allowed; Q = 0, the extremal and super-extremal cases are excluded). U p = {(r, θ) : r > r₊, 0 < θ < π} with r₊ = M + √(M² − a² − Q²); domKN p.M p.a p.Q = {x ∈ ℝ⁴ : (x¹, x²) ∈ U p} (t and φ arbitrary real numbers; no horizon, axis or chart gluing). ω, m real (0 allowed); u C^∞ on U p.
--
--   **中文摘要** 单模式场的四个标架方向导数恰为 III 在 j=0 的 Dop、DopDag、LopDag、Lop（带显式前因子）；ω、m 为实数，允许 0。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V01.lean#L46-L69; SHA-256 163c0780f59c9198d1097ef71bf5f7b6a5671f5ab3e49027f671fc9cbbb4a34a. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
open scoped ComplexConjugate Matrix ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.KN (gKN giKN faradayKN domReg domKN)

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.v01_modes (p : Hintz2026.SubextremalKN) (om mm : ℝ) {u : (Fin 2 → ℝ) → ℂ}
    (hu : ContDiffOn ℝ ∞ u (Hintz2026.U p)) :
    ContDiffOn ℝ ∞ (modeField om mm u) (domKN p.M p.a p.Q) ∧
    ∀ x ∈ domKN p.M p.a p.Q,
      (∀ i : Fin 4, HasDerivAt (fun s : ℝ => modeField om mm u (Function.update x i s))
        (cpdC i (modeField om mm u) x) (x i)) ∧
      toRT x ∈ Hintz2026.U p ∧ phaseP om mm x ≠ 0 ∧
      cdir (knFrame p.M p.a p.Q x 0) (modeField om mm u) x =
        phaseP om mm x * Hintz2026.Dop p 0 om mm u (toRT x) ∧
      cdir (knFrame p.M p.a p.Q x 1) (modeField om mm u) x =
        phaseP om mm x * (-((KN.Del p.M p.a p.Q (x 1) / (2 * KN.Sig p.a (x 1) (x 2)) : ℝ) : ℂ)) *
          Hintz2026.DopDag p 0 om mm u (toRT x) ∧
      cdir (knFrame p.M p.a p.Q x 2) (modeField om mm u) x =
        phaseP om mm x / (((Real.sqrt 2 : ℝ) : ℂ) * Hintz2026.rhoBar p (toRT x)) *
          Hintz2026.LopDag p 0 om mm u (toRT x) ∧
      cdir (knFrame p.M p.a p.Q x 3) (modeField om mm u) x =
        phaseP om mm x / (((Real.sqrt 2 : ℝ) : ℂ) * Hintz2026.rhoBarStar p (toRT x)) *
          Hintz2026.Lop p 0 om mm u (toRT x) := by sorry
