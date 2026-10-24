-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_domKN_Del_pos
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.domKN_Del_pos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-23T10:18:49.598706+00:00
-- url     : https://prove2.me/theorems/06d7aaba-8f2a-4de2-8218-7f3ce51f2051
-- title:
--   Δ > 0 on the exterior
-- statement:
--   Δ > 0 on the exterior
--
--   On domKN M a Q (r > r₊), Δ(r) > 0 for every real M, a, Q (no sub-extremality needed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 外域上 Δ>0。
-- source:
--   He Wang, Exact Spacetime Atlas V: From Linearized Einstein–Maxwell Equations to Kerr–Newman Radiation Systems. Local source, no public repository; commit b8cd107a558e153ed41fb4972ac5315499d14778; Atlas/EinsteinMaxwell/KN/Domain.lean#L71-L81; SHA-256 2cba50578710c01bc97b197588f366c9fd153ed1add83d7d7577383f23a9ccce. Registered definitions: mission/PHYSICS_BOUNDARY.md (§K–§M); literature: P. Hintz, arXiv:2609.33661 (v1); Mark–Yang–Zimmerman–Chen, arXiv:1409.5800 (v1).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_InAtoms
open Real
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
open ExactVacuumAtlas.Kerr.In (Ui Wi)

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.domKN_Del_pos {M a Q : ℝ} {x : Pt 4} (hx : x ∈ domKN M a Q) :
    0 < Del M a Q (x 1) := by sorry
