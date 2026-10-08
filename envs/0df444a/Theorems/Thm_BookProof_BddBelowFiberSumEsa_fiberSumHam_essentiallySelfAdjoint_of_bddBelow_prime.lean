-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_essentiallySelfAdjoint_of_bddBelow_prime
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T16:27:06.955384+00:00
-- url     : https://prove2.me/theorems/7a3880ee-a934-40d9-9d97-822937192d62
-- title:
--   The Lean 4 theorem `fiberSumHam_essentiallySelfAdjoint_of_bddBelow_prime` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_essentiallySelfAdjoint_of_bddBelow'` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow'
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.BddBelowFiberSumEsa

variable {ι : Type*}



open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow_prime (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hbdd : ∀ i, BddBelow (Set.range (V i))) :
    EssentiallySelfAdjointOn (fiberCore ι) (fiberSumHam V hV) := by sorry
