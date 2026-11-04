-- Prove2me | Theorems.Thm_BookProof_ChapterH8_krylovOrthonormal_nested
-- name    : BookProof.ChapterH8.krylovOrthonormal_nested
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:46:09.803879+00:00
-- url     : https://prove2.me/theorems/a94dee21-5c22-4f06-8279-826ee24cac9e
-- title:
--   The Lean 4 theorem `krylovOrthonormal_nested` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylovOrthonormal_nested` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.krylovOrthonormal_nested
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

theorem BookProof.ChapterH8.krylovOrthonormal_nested {H : E →ₗ[ℂ] E} {v : E} {m n : ℕ} (hmn : m ≤ n)
    (i : Fin m) :
    krylovOrthonormalSeq H v (i : ℕ)
      = krylovOrthonormalSeq H v ((Fin.castLE hmn i : Fin n) : ℕ) := by sorry
