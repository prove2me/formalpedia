-- Prove2me | Theorems.Thm_BookProof_OdeUnitaryFlow_mob_neg_mob
-- name    : BookProof.OdeUnitaryFlow.mob_neg_mob
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:41:30.517984+00:00
-- url     : https://prove2.me/theorems/d4f65ebb-3c7f-4fcd-b036-8867ef3460a3
-- title:
--   `BookProof.OdeUnitaryFlow.mob_neg_mob` (t x : ℝ) (hx : x ∈ flowDom t) : mob (-t) (mob t x) = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOdeUnitaryFlow`.
--
--   `BookProof.OdeUnitaryFlow.mob_neg_mob` (t x : ℝ) (hx : x ∈ flowDom t) : mob (-t) (mob t x) = x
--
--   Formalization note: Lean 4 identifier `BookProof.OdeUnitaryFlow.mob_neg_mob`.

-- Generated from ChapterOdeUnitaryFlow.lean — theorem BookProof.OdeUnitaryFlow.mob_neg_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
open BookProof.OdeUnitaryFlow



open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem BookProof.OdeUnitaryFlow.mob_neg_mob (t x : ℝ) (hx : x ∈ flowDom t) : mob (-t) (mob t x) = x := by sorry
