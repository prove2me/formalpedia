-- Prove2me | Theorems.Thm_BookProof_ChapterH8_coordIncl_single
-- name    : BookProof.ChapterH8.coordIncl_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:49:39.774808+00:00
-- url     : https://prove2.me/theorems/09327d79-bddf-497d-bfff-8d85e062a7a6
-- title:
--   The Lean 4 theorem `coordIncl_single` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coordIncl_single` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.coordIncl_single
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

theorem BookProof.ChapterH8.coordIncl_single {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    coordIncl hmn (EuclideanSpace.single i (1 : ℂ))
      = EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ) := by sorry
