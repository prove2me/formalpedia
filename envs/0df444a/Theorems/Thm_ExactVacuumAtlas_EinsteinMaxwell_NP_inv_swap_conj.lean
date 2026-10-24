-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_NP_inv_swap_conj
-- name    : ExactVacuumAtlas.EinsteinMaxwell.NP.inv_swap_conj
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:19:50.120985+00:00
-- url     : https://prove2.me/theorems/21d1b594-11ac-49ea-9761-65acc0ed786b
-- title:
--   Inverse of a matrix with the real pattern
-- statement:
--   Inverse of a matrix with the real pattern
--
--   If E has the reality pattern e_{swap23 A} = conj e_A, its inverse satisfies Θ_{swap23 C} = conj Θ_C.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 实性模式矩阵的逆仍有共轭模式。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/NP/V03Realize.lean#L77-L94; SHA-256 a3ba6bed8a3f274a79c27da921d2b891c251411ce219cec944034d43e884039b. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

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
import Definitions.Def_Atlas_EinsteinMaxwell_NP_V03Realize
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

theorem ExactVacuumAtlas.EinsteinMaxwell.NP.inv_swap_conj {T : Matrix (Fin 4) (Fin 4) ℂ} (hT : ∀ μ A, T μ (swap23 A) = conj (T μ A))
    (hdet : T.det ≠ 0) (C μ : Fin 4) : T⁻¹ (swap23 C) μ = conj (T⁻¹ C μ) := by sorry
