-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_hasDerivAt_invMap
-- name    : BookProof.OdeUnitaryFlow.hasDerivAt_invMap
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:43:21.151686+00:00
-- url     : https://prove2.me/theorems/b54013ff-0cb0-45ce-b7cc-10e28ccf0d1f
-- title:
--   `BookProof.OdeUnitaryFlow.hasDerivAt_invMap` {x : ℝ} (hx : x ≠ 0) : HasDerivAt invMap ((x ^ 2)⁻¹) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.hasDerivAt_invMap` {x : ℝ} (hx : x ≠ 0) : HasDerivAt invMap ((x ^ 2)⁻¹) x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.hasDerivAt_invMap`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.hasDerivAt_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.hasDerivAt_invMap {x : ℝ} (hx : x ≠ 0) : HasDerivAt invMap ((x ^ 2)⁻¹) x := by sorry
