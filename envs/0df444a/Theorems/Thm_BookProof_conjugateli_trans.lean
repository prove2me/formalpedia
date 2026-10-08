-- Prove2me | Theorems.Thm_BookProof_conjugateli_trans
-- name    : BookProof.conjugateli_trans
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T08:25:31.681376+00:00
-- url     : https://prove2.me/theorems/577d5a66-f4e0-4ecd-b621-98580f38448d
-- title:
--   `BookProof.conjugateli_trans` (Θ : E ≃ₗᵢ[R] E') (A B : E ≃ₗᵢ[R] E) : conjugateₗᵢ Θ (A.trans B) = (conjugateₗᵢ Θ A).trans (conjugateₗᵢ Θ B)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4`.
--
--   `BookProof.conjugateli_trans` (Θ : E ≃ₗᵢ[R] E') (A B : E ≃ₗᵢ[R] E) : conjugateₗᵢ Θ (A.trans B) = (conjugateₗᵢ Θ A).trans (conjugateₗᵢ Θ B)
--
--   Formalization note: Lean 4 identifier `BookProof.conjugateli_trans`.

-- Generated from ChapterA4.lean — theorem BookProof.conjugateₗᵢ_trans
import Mathlib
import Definitions.Def_ChapterA4
open BookProof



open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

theorem BookProof.conjugateli_trans (Θ : E ≃ₗᵢ[R] E') (A B : E ≃ₗᵢ[R] E) :
    conjugateₗᵢ Θ (A.trans B) = (conjugateₗᵢ Θ A).trans (conjugateₗᵢ Θ B) := by sorry
