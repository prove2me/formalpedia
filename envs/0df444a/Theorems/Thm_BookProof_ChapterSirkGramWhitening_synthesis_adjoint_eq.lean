-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_synthesis_adjoint_eq
-- name    : BookProof.ChapterSirkGramWhitening.synthesis_adjoint_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:44:52.24011+00:00
-- url     : https://prove2.me/theorems/c9b25244-46ab-4b7c-b807-069820998932
-- title:
--   {m : ℕ} (w : Fin m → E) (x : E) : (ContinuousLinearMap.adjoint (synthesis w)) x = (WithLp.toLp 2 fun i => ⟪w i, x⟫_ℂ)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.synthesis_adjoint_eq` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.synthesis_adjoint_eq
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.synthesis_adjoint_eq {m : ℕ} (w : Fin m → E) (x : E) :
    (ContinuousLinearMap.adjoint (synthesis w)) x = (WithLp.toLp 2 fun i => ⟪w i, x⟫_ℂ) := by sorry
