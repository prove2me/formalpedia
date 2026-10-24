-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_phiC_eq
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.phiC_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:24:18.134245+00:00
-- url     : https://prove2.me/theorems/d907c0b0-a20a-479b-aa61-1f926318aa49
-- title:
--   Coulomb component Φ₁
-- statement:
--   Coulomb component Φ₁
--
--   On domReg: phiC = Φ₁ = Q/(2 q̄²), q̄ = r − i a cos θ.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** Φ₁=Q/(2q̄²)。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/KNFaraday.lean#L181-L198; SHA-256 cab1226e82c48431de6bcae27caa3784dedabf5a67e7c2bb040fee2dce482b03. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_Kerr_InAtoms
open Real
open scoped ComplexConjugate Matrix
open ExactVacuumAtlas.EinsteinMaxwell.KN (Sig Del faradayKN domReg)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.NP
variable {M a Q : ℝ} {x : Pt 4}

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.phiC_eq (hx : x ∈ domReg M a Q) : phiC M a Q x = (Q : ℂ) / (2 * qbarK a x ^ 2) := by sorry
