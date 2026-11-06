-- Prove2me | Theorems.Thm_BookProof_ChapterG2_haarAverage_invariant
-- name    : BookProof.ChapterG2.haarAverage_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:10:16.982509+00:00
-- url     : https://prove2.me/theorems/d2ecfeb5-dc56-421c-af1d-90e3acfed573
-- title:
--   `BookProof.ChapterG2.haarAverage_invariant` [MeasurableMul G] (f : X → ℝ) (g : G) (x : X) : haarAverage (μG
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.haarAverage_invariant` [MeasurableMul G] (f : X → ℝ) (g : G) (x : X) : haarAverage (μG
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.haarAverage_invariant`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.haarAverage_invariant
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

theorem BookProof.ChapterG2.haarAverage_invariant [MeasurableMul G] (f : X → ℝ) (g : G) (x : X) :
    haarAverage (μG := μG) f (g • x) = haarAverage (μG := μG) f x := by sorry
