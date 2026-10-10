-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_mob_mem_flowDom_neg
-- name    : BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:38.639254+00:00
-- url     : https://prove2.me/theorems/270e5d3d-3744-41e1-9b73-730ad5659d51
-- title:
--   `BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg` (t x : ℝ) (hx : x ∈ flowDom t) : mob t x ∈ flowDom (-t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg` (t x : ℝ) (hx : x ∈ flowDom t) : mob t x ∈ flowDom (-t)
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.mob_mem_flowDom_neg (t x : ℝ) (hx : x ∈ flowDom t) : mob t x ∈ flowDom (-t) := by sorry
