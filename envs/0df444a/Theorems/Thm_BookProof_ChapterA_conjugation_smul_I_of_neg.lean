-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjugation_smul_I_of_neg
-- name    : BookProof.ChapterA.conjugation_smul_I_of_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:37:08.295612+00:00
-- url     : https://prove2.me/theorems/601697ec-9989-4a66-8dfb-79cbde7b77c0
-- title:
--   `BookProof.ChapterA.conjugation_smul_I_of_neg` (θ : AntiUnitary V) {y : V} (hy : θ y = -y) : θ (Complex.I • y) = Complex.I • y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1`.
--
--   `BookProof.ChapterA.conjugation_smul_I_of_neg` (θ : AntiUnitary V) {y : V} (hy : θ y = -y) : θ (Complex.I • y) = Complex.I • y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjugation_smul_I_of_neg`.

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.conjugation_smul_I_of_neg
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem BookProof.ChapterA.conjugation_smul_I_of_neg (θ : AntiUnitary V) {y : V} (hy : θ y = -y) :
    θ (Complex.I • y) = Complex.I • y := by sorry
