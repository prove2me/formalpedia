-- Prove2me | Theorems.Thm_BookProof_ChapterH8_krylov_li_of_le
-- name    : BookProof.ChapterH8.krylov_li_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T06:37:04.293743+00:00
-- url     : https://prove2.me/theorems/50baab02-3716-433a-99a0-40dd8e21eb95
-- title:
--   krylov_li_of_le
-- statement:
--   Formal statement of `BookProof.ChapterH8.krylov_li_of_le` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterH8Bases.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.krylov_li_of_le
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
open BookProof.ChapterH8

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6




open ContinuousLinearMap

theorem BookProof.ChapterH8.krylov_li_of_le {H : E →ₗ[ℂ] E} {v : E} {m n : ℕ} (hmn : m ≤ n)
    (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    LinearIndependent ℂ (fun i : Fin m => (H ^ (i : ℕ)) v) := by sorry
