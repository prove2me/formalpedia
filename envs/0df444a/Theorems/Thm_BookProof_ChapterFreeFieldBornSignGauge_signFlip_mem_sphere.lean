-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_signFlip_mem_sphere
-- name    : BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:32:50.779982+00:00
-- url     : https://prove2.me/theorems/cbefbb94-e09b-45bf-8b7f-781bdee2728b
-- title:
--   `BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere` {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignGauge`.
--
--   `BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere` {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : signFlip s x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere`.

-- Generated from ChapterFreeFieldBornSignGauge.lean — theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignGauge

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn

theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_mem_sphere {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    signFlip s x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by sorry
