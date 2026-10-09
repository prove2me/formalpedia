-- Prove2me | Theorems.Thm_BookProof_ChapterG_gaugeOrbit_eq_fiber
-- name    : BookProof.ChapterG.gaugeOrbit_eq_fiber
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:44:44.778746+00:00
-- url     : https://prove2.me/theorems/f3bdddac-d5a4-4066-a90f-7702442efce9
-- title:
--   `BookProof.ChapterG.gaugeOrbit_eq_fiber` {X Y : Type*} (π : X → Y) (x : X) : MulAction.orbit (gaugeGroup π) x = π ⁻¹' {π x}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.gaugeOrbit_eq_fiber` {X Y : Type*} (π : X → Y) (x : X) : MulAction.orbit (gaugeGroup π) x = π ⁻¹' {π x}
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.gaugeOrbit_eq_fiber`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.gaugeOrbit_eq_fiber
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix

theorem BookProof.ChapterG.gaugeOrbit_eq_fiber {X Y : Type*} (π : X → Y) (x : X) :
    MulAction.orbit (gaugeGroup π) x = π ⁻¹' {π x} := by sorry
