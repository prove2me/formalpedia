-- Prove2me | Theorems.Thm_BookProof_ChapterH8_coordIncl_adjoint_comp
-- name    : BookProof.ChapterH8.coordIncl_adjoint_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T03:23:30.105149+00:00
-- url     : https://prove2.me/theorems/f324d9e9-f25b-4a6b-9489-3379e28e8e8f
-- title:
--   The Lean 4 theorem `coordIncl_adjoint_comp` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coordIncl_adjoint_comp` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.coordIncl_adjoint_comp
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

theorem BookProof.ChapterH8.coordIncl_adjoint_comp {m n : ℕ} (hmn : m ≤ n) :
    (adjoint (coordIncl hmn)).comp (coordIncl hmn)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by sorry
