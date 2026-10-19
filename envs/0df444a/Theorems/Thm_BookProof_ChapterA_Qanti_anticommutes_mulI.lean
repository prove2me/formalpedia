-- Prove2me | Theorems.Thm_BookProof_ChapterA_Qanti_anticommutes_mulI
-- name    : BookProof.ChapterA.Qanti_anticommutes_mulI
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:17:21.350098+00:00
-- url     : https://prove2.me/theorems/c0c206ad-903d-4835-b3ba-7b31d638fe3b
-- title:
--   `BookProof.ChapterA.Qanti_anticommutes_mulI` (S : V →L[ℝ] V) (x : V) : Qanti S (Complex.I • x) = -(Complex.I • Qanti S x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.Qanti_anticommutes_mulI` (S : V →L[ℝ] V) (x : V) : Qanti S (Complex.I • x) = -(Complex.I • Qanti S x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Qanti_anticommutes_mulI`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.Qanti_anticommutes_mulI
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Qanti_anticommutes_mulI (S : V →L[ℝ] V) (x : V) :
    Qanti S (Complex.I • x) = -(Complex.I • Qanti S x) := by sorry
