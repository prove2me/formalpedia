-- Prove2me | Theorems.Thm_BookProof_ChapterH8_li_Fin_of_le
-- name    : BookProof.ChapterH8.li_Fin_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:48:45.320635+00:00
-- url     : https://prove2.me/theorems/d2a0845f-1ef1-4625-a456-1da7b376a746
-- title:
--   The Lean 4 theorem `li_Fin_of_le` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `li_Fin_of_le` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.li_Fin_of_le
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

theorem BookProof.ChapterH8.li_Fin_of_le (f : ℕ → E) {m n : ℕ} (hmn : m ≤ n)
    (hli : LinearIndependent ℂ (fun i : Fin n => f i)) :
    LinearIndependent ℂ (fun i : Fin m => f i) := by sorry
