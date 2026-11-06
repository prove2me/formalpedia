-- Prove2me | Theorems.Thm_BookProof_ChapterG2_haarAverage_idempotent
-- name    : BookProof.ChapterG2.haarAverage_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:10:23.402204+00:00
-- url     : https://prove2.me/theorems/b016ad03-c48f-49e9-a641-f1ab6f2bbda9
-- title:
--   `BookProof.ChapterG2.haarAverage_idempotent` [MeasurableMul G] (f : X → ℝ) : haarAverage (μG
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.haarAverage_idempotent` [MeasurableMul G] (f : X → ℝ) : haarAverage (μG
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.haarAverage_idempotent`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.haarAverage_idempotent
import Mathlib
import Definitions.Def_ChapterG2
import Definitions.Def_ChapterG
open BookProof.ChapterG
open BookProof.ChapterG2


open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG2.haarAverage_idempotent [MeasurableMul G] (f : X → ℝ) :
    haarAverage (μG := μG) (haarAverage (μG := μG) f) = haarAverage (μG := μG) f := by sorry
