-- Prove2me | Theorems.Thm_BookProof_conjugateli_symm
-- name    : BookProof.conjugateli_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T08:25:21.176711+00:00
-- url     : https://prove2.me/theorems/d5fd5db5-f752-4ac1-8d74-ceff95e09847
-- title:
--   `BookProof.conjugateli_symm` (Θ : E ≃ₗᵢ[R] E') (A : E ≃ₗᵢ[R] E) : (conjugateₗᵢ Θ A).symm = conjugateₗᵢ Θ A.symm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4`.
--
--   `BookProof.conjugateli_symm` (Θ : E ≃ₗᵢ[R] E') (A : E ≃ₗᵢ[R] E) : (conjugateₗᵢ Θ A).symm = conjugateₗᵢ Θ A.symm
--
--   Formalization note: Lean 4 identifier `BookProof.conjugateli_symm`.

-- Generated from ChapterA4.lean — theorem BookProof.conjugateₗᵢ_symm
import Mathlib
import Definitions.Def_ChapterA4
open BookProof



open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

theorem BookProof.conjugateli_symm (Θ : E ≃ₗᵢ[R] E') (A : E ≃ₗᵢ[R] E) :
    (conjugateₗᵢ Θ A).symm = conjugateₗᵢ Θ A.symm := by sorry
