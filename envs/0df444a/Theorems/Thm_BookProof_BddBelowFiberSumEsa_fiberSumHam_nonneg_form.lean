-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_nonneg_form
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_nonneg_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:46.025442+00:00
-- url     : https://prove2.me/theorems/dc96724f-a553-4388-ae7b-bd6918b75b4a
-- title:
--   The Lean 4 theorem `fiberSumHam_nonneg_form` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_nonneg_form` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_nonneg_form
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.WallEsaSemibounded
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_nonneg_form (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (hnn : ∀ i x, 0 ≤ V i x) :
    SemiboundedBelowOn (fiberCore ι) (fiberSumHam V hV) 0 := by sorry
