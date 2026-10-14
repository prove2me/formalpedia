-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeParametrization_orbit_eq_fiber
-- name    : BookProof.ChapterGaugeParametrization.orbit_eq_fiber
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:46:12.624273+00:00
-- url     : https://prove2.me/theorems/9726f6d1-f1a8-488c-b300-6c182f43ccbe
-- title:
--   `BookProof.ChapterGaugeParametrization.orbit_eq_fiber` (π : X → Y) (x : X) : MulAction.orbit (fiberGauge π) x = π ⁻¹' {π x}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeParametrization`.
--
--   `BookProof.ChapterGaugeParametrization.orbit_eq_fiber` (π : X → Y) (x : X) : MulAction.orbit (fiberGauge π) x = π ⁻¹' {π x}
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeParametrization.orbit_eq_fiber`.

-- Generated from ChapterGaugeParametrization.lean — theorem BookProof.ChapterGaugeParametrization.orbit_eq_fiber
import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
open BookProof.ChapterGaugeParametrization



open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

theorem BookProof.ChapterGaugeParametrization.orbit_eq_fiber (π : X → Y) (x : X) :
    MulAction.orbit (fiberGauge π) x = π ⁻¹' {π x} := by sorry
