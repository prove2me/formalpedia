-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ricciOf_eq_zero_of_einsteinMaxwell
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ricciOf_eq_zero_of_einsteinMaxwell
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:40.359823+00:00
-- url     : https://prove2.me/theorems/bb114611-464d-4bbf-bee3-1b18e333c2db
-- title:
--   E = 0 with F = 0 gives Ricci = 0
-- statement:
--   E = 0 with F = 0 gives Ricci = 0
--
--   At a point with symmetric g, true inverse, F = 0 and all E_ab = 0: all ricciOf components vanish (trace argument in 4D).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** F=0 且 E=0 推出 Ricci=0（4 维取迹）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Certificate.lean#L98-L119; SHA-256 96047b8402974e172119af74b269b2642fe03c56261d6475022bc193053e6c50. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
open scoped ContDiff

theorem ExactVacuumAtlas.EinsteinMaxwell.ricciOf_eq_zero_of_einsteinMaxwell {g ginv : Metric 4} {F : TwoForm 4} {x : Pt 4}
    (hs : ∀ i j, g i j x = g j i x) (hinv : metricMatrix ginv x * metricMatrix g x = 1)
    (hF : ∀ i j, F i j x = 0) (hE : ∀ i j, einsteinMaxwell g ginv F i j x = 0) (i j : Fin 4) :
    ricciOf g ginv i j x = 0 := by sorry
