-- Prove2me | Theorems.Thm_BookProof_ChapterG_haarAverage_of_invariant
-- name    : BookProof.ChapterG.haarAverage_of_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T14:09:16.92821+00:00
-- url     : https://prove2.me/theorems/967346a1-3f06-4148-884c-9fc2de796c67
-- title:
--   `BookProof.ChapterG.haarAverage_of_invariant` (f : X → ℝ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) : haarAverage (μG
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.haarAverage_of_invariant` (f : X → ℝ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) : haarAverage (μG
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.haarAverage_of_invariant`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.haarAverage_of_invariant
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix














open MeasureTheory










variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG.haarAverage_of_invariant (f : X → ℝ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) :
    haarAverage (μG := μG) f = f := by sorry
