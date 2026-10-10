-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_invMap_mob
-- name    : BookProof.OdeUnitaryFlow.invMap_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:42:48.575583+00:00
-- url     : https://prove2.me/theorems/b2ecf130-efc0-4623-bffb-0a6aa9cbc403
-- title:
--   `BookProof.OdeUnitaryFlow.invMap_mob` {t x : ℝ} (hx : x ≠ 0) : invMap (mob t x) = invMap x - t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.invMap_mob` {t x : ℝ} (hx : x ≠ 0) : invMap (mob t x) = invMap x - t
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.invMap_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.invMap_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.invMap_mob {t x : ℝ} (hx : x ≠ 0) :
    invMap (mob t x) = invMap x - t := by sorry
