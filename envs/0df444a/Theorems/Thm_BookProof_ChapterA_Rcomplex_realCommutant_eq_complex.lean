-- Prove2me | Theorems.Thm_BookProof_ChapterA_Rcomplex_realCommutant_eq_complex
-- name    : BookProof.ChapterA.Rcomplex_realCommutant_eq_complex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:18:29.168324+00:00
-- url     : https://prove2.me/theorems/61c3b539-f713-4c36-83a2-66e132a413e5
-- title:
--   `BookProof.ChapterA.Rcomplex_realCommutant_eq_complex` (M : System ℂ V) (hSchur : IsSchurFull M) (hNo : NoAntilinearCommutant M) (S : V →L[ℝ] V) : RealCommutes M S ↔ ∃ c : ℂ, S = c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.Rcomplex_realCommutant_eq_complex` (M : System ℂ V) (hSchur : IsSchurFull M) (hNo : NoAntilinearCommutant M) (S : V →L[ℝ] V) : RealCommutes M S ↔ ∃ c : ℂ, S = cembed c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Rcomplex_realCommutant_eq_complex`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.Rcomplex_realCommutant_eq_complex
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Rcomplex_realCommutant_eq_complex (M : System ℂ V) (hSchur : IsSchurFull M)
    (hNo : NoAntilinearCommutant M) (S : V →L[ℝ] V) :
    RealCommutes M S ↔ ∃ c : ℂ, S = cembed c := by sorry
