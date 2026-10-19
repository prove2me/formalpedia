-- Prove2me | Theorems.Thm_BookProof_ChapterA_realCommutes_algebraMap
-- name    : BookProof.ChapterA.realCommutes_algebraMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:05.370755+00:00
-- url     : https://prove2.me/theorems/9a89e15d-3945-4cf7-b05f-7e4e216ced7d
-- title:
--   `BookProof.ChapterA.realCommutes_algebraMap` (M : System ℂ V) (r : ℝ) : RealCommutes M (algebraMap ℝ (V →L[ℝ] V) r)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.realCommutes_algebraMap` (M : System ℂ V) (r : ℝ) : RealCommutes M (algebraMap ℝ (V →L[ℝ] V) r)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.realCommutes_algebraMap`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.realCommutes_algebraMap
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.realCommutes_algebraMap (M : System ℂ V) (r : ℝ) :
    RealCommutes M (algebraMap ℝ (V →L[ℝ] V) r) := by sorry
