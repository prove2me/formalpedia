-- Prove2me | Theorems.Thm_BookProof_ChapterA_cembed_apply
-- name    : BookProof.ChapterA.cembed_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:15:53.352335+00:00
-- url     : https://prove2.me/theorems/f03136e4-4507-4b26-8bf7-6d1013e0484c
-- title:
--   `BookProof.ChapterA.cembed_apply` (c : ℂ) (x : V) : (cembed c : V →L[ℝ] V) x = c • x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.cembed_apply` (c : ℂ) (x : V) : (cembed c : V →L[ℝ] V) x = c • x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.cembed_apply`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.cembed_apply
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.cembed_apply (c : ℂ) (x : V) : (cembed c : V →L[ℝ] V) x = c • x := by sorry
