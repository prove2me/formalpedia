-- Prove2me | Theorems.Thm_BookProof_ChapterA_realCommutes_smul
-- name    : BookProof.ChapterA.realCommutes_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:14:55.991371+00:00
-- url     : https://prove2.me/theorems/8649c8c1-3815-42f3-a62f-1755e2c0e470
-- title:
--   `BookProof.ChapterA.realCommutes_smul` {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S) (r : ℝ) : RealCommutes M (r • S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.realCommutes_smul` {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S) (r : ℝ) : RealCommutes M (r • S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.realCommutes_smul`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.realCommutes_smul
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.realCommutes_smul {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S)
    (r : ℝ) : RealCommutes M (r • S) := by sorry
