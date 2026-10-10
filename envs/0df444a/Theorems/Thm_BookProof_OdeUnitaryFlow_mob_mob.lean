-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_mob_mob
-- name    : BookProof.OdeUnitaryFlow.mob_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:48.093544+00:00
-- url     : https://prove2.me/theorems/dfee6c42-8585-45d6-a7c3-da60ad8d03c1
-- title:
--   `BookProof.OdeUnitaryFlow.mob_mob` (s t x : ℝ) (hx : 1 + t * x ≠ 0) (hst : 1 + (s + t) * x ≠ 0) : mob s (mob t x) = mob (s + t) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.mob_mob` (s t x : ℝ) (hx : 1 + t * x ≠ 0) (hst : 1 + (s + t) * x ≠ 0) : mob s (mob t x) = mob (s + t) x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.mob_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.mob_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.mob_mob (s t x : ℝ) (hx : 1 + t * x ≠ 0) (hst : 1 + (s + t) * x ≠ 0) :
    mob s (mob t x) = mob (s + t) x := by sorry
