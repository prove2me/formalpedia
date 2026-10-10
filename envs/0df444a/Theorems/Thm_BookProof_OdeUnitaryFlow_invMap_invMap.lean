-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_invMap_invMap
-- name    : BookProof.OdeUnitaryFlow.invMap_invMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:42:37.741993+00:00
-- url     : https://prove2.me/theorems/a3ab8778-8526-4240-a94a-27ae205f0bbb
-- title:
--   `BookProof.OdeUnitaryFlow.invMap_invMap` {x : ℝ} (hx : x ≠ 0) : invMap (invMap x) = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.invMap_invMap` {x : ℝ} (hx : x ≠ 0) : invMap (invMap x) = x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.invMap_invMap`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.invMap_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.invMap_invMap {x : ℝ} (hx : x ≠ 0) : invMap (invMap x) = x := by sorry
