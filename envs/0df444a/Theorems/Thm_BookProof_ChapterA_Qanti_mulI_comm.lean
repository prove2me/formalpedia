-- Prove2me | Theorems.Thm_BookProof_ChapterA_Qanti_mulI_comm
-- name    : BookProof.ChapterA.Qanti_mulI_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:17:09.71398+00:00
-- url     : https://prove2.me/theorems/9d955db7-8173-4194-972e-30d05d92b9f3
-- title:
--   `BookProof.ChapterA.Qanti_mulI_comm` (S : V →L[ℝ] V) : mulI * Qanti S = -(Qanti S * mulI)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.Qanti_mulI_comm` (S : V →L[ℝ] V) : mulI * Qanti S = -(Qanti S * mulI)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Qanti_mulI_comm`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.Qanti_mulI_comm
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Qanti_mulI_comm (S : V →L[ℝ] V) : mulI * Qanti S = -(Qanti S * mulI) := by sorry
