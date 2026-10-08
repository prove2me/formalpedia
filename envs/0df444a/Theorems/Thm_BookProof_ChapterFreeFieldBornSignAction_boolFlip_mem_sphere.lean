-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_boolFlip_mem_sphere
-- name    : BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:17:18.343898+00:00
-- url     : https://prove2.me/theorems/6ec03985-dd55-4ef1-b30f-cf0f1d4658e8
-- title:
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere` (b : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : boolFli
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignAction`.
--
--   `BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere` (b : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : boolFlip b x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere`.

-- Generated from ChapterFreeFieldBornSignAction.lean — theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

theorem BookProof.ChapterFreeFieldBornSignAction.boolFlip_mem_sphere (b : Fin n → Bool) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    boolFlip b x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by sorry
