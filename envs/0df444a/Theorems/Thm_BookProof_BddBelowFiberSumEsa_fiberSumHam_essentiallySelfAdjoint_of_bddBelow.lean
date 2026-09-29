-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_essentiallySelfAdjoint_of_bddBelow
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:19.953346+00:00
-- url     : https://prove2.me/theorems/ea676491-cb2d-4365-a590-c82961f47aa4
-- title:
--   The Lean 4 theorem `fiberSumHam_essentiallySelfAdjoint_of_bddBelow` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_essentiallySelfAdjoint_of_bddBelow` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hbdd : ∀ i, ∃ K : ℝ, ∀ x, -K ≤ V i x) :
    EssentiallySelfAdjointOn (fiberCore ι) (fiberSumHam V hV) := by sorry
