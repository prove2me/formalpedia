-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_image_mob
-- name    : BookProof.OdeUnitaryFlow.image_mob
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:42:59.311313+00:00
-- url     : https://prove2.me/theorems/ed7ba6d5-fe67-40a8-a713-cd1dc3d118a0
-- title:
--   `BookProof.OdeUnitaryFlow.image_mob` (t : ℝ) : mob t '' flowDom t = flowDom (-t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.image_mob` (t : ℝ) : mob t '' flowDom t = flowDom (-t)
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.image_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.image_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.image_mob (t : ℝ) : mob t '' flowDom t = flowDom (-t) := by sorry
