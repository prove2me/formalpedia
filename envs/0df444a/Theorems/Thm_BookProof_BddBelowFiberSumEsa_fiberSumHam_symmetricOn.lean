-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_symmetricOn
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:27.236387+00:00
-- url     : https://prove2.me/theorems/d8ac62a5-7e5f-4709-bb32-07076764ce3f
-- title:
--   The Lean 4 theorem `fiberSumHam_symmetricOn` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_symmetricOn` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_symmetricOn (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) :
    SymmetricOn (fiberCore ι) (fiberSumHam V hV) := by sorry
