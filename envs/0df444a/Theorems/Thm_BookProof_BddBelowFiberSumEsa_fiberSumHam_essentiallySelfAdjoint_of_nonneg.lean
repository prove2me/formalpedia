-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_essentiallySelfAdjoint_of_nonneg
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:25.214822+00:00
-- url     : https://prove2.me/theorems/7343a0ee-6920-4934-bfce-885480b4d84d
-- title:
--   The Lean 4 theorem `fiberSumHam_essentiallySelfAdjoint_of_nonneg` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_essentiallySelfAdjoint_of_nonneg` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_nonneg
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_nonneg (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (hnn : ∀ i x, 0 ≤ V i x) :
    EssentiallySelfAdjointOn (fiberCore ι) (fiberSumHam V hV) := by sorry
