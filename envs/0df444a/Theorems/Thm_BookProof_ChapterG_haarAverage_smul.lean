-- Prove2me | Theorems.Thm_BookProof_ChapterG_haarAverage_smul
-- name    : BookProof.ChapterG.haarAverage_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T14:09:09.810451+00:00
-- url     : https://prove2.me/theorems/c11bee2e-5cc7-46c8-92a5-524634d49eee
-- title:
--   `BookProof.ChapterG.haarAverage_smul` [MeasurableMul G] (f : X → ℝ) (g₀ : G) (x : X) : haarAverage (μG
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.haarAverage_smul` [MeasurableMul G] (f : X → ℝ) (g₀ : G) (x : X) : haarAverage (μG
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.haarAverage_smul`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.haarAverage_smul
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix














open MeasureTheory










variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG.haarAverage_smul [MeasurableMul G]
    (f : X → ℝ) (g₀ : G) (x : X) :
    haarAverage (μG := μG) f (g₀ • x) = haarAverage (μG := μG) f x := by sorry
