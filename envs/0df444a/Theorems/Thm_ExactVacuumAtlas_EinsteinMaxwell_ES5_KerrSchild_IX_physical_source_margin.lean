-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_IX_physical_source_margin
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_source_margin
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-22T02:59:48.108813+00:00
-- url     : https://prove2.me/theorems/5a85788f-afec-4197-8c13-66a9f2f91ef8
-- title:
--   Physical actual-source coefficient margin
-- statement:
--   Physical actual-source coefficient margin
--
--   The coefficient multiplying the actual-source defect has a strictly positive margin on the compactified source domain.
--
--   **Scope.** Exact Spacetime Atlas IX physical actual-source interface. The registered B3 data structure records the closed actual source `srcMbar`, generic completion `qMcK`, four weighted residuals, the VIII20 absorption identity, and its positive coefficient margin on a compact source domain. The theorem concludes the actual-source equality when those physical residuals vanish. Metric-valued Ricci correspondence and an implicit-function theorem certificate remain later gates.
-- source:
--   He Wang, Exact Spacetime Atlas IX analytic bridge. Local source, commit 8fc44e0bf5f0; Atlas/EinsteinMaxwell/ES5/KerrSchild/IX/Main.lean#L32-L41; SHA-256 254d5388ccac0e3abdd262a940146f81e499d06c45935e012402dee4dc0fa46b. Registered definitions: mission/PHYSICS_BOUNDARY.md, notes/B3_POLICY.md. Analytic source and residual bridge: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_IX_PhysicalSource

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.IX.physical_source_margin
    (kg : Set ℝ)
    (srcMbar : ℝ → ℝ) (qMcK : ℝ → ℝ)
    (wF : ℝ → ℝ) (wMc : ℝ → ℝ) (wC : ℝ → ℝ) (wA : ℝ → ℝ)
    (lamF : ℝ → ℝ) (lamM : ℝ → ℝ) (lamC : ℝ → ℝ) (lamA : ℝ → ℝ)
    (hD : PhysicalSourceData kg srcMbar qMcK wF wMc wC wA lamF lamM lamC lamA) :
    PhysicalMarginOn kg lamM := by sorry
