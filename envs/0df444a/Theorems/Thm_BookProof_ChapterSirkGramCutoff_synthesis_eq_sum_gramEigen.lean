-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_synthesis_eq_sum_gramEigen
-- name    : BookProof.ChapterSirkGramCutoff.synthesis_eq_sum_gramEigen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:21:52.69521+00:00
-- url     : https://prove2.me/theorems/2e9cba0c-983f-4c7e-ac62-745c8d869845
-- title:
--   (c : EuclideanSpace ℂ (Fin m)) : synthesis w c = ∑ k, ⟪u k, c⟫_ℂ • synthesis w (u k)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.synthesis_eq_sum_gramEigen` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.synthesis_eq_sum_gramEigen
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem BookProof.ChapterSirkGramCutoff.synthesis_eq_sum_gramEigen (c : EuclideanSpace ℂ (Fin m)) :
    synthesis w c = ∑ k, ⟪u k, c⟫_ℂ • synthesis w (u k) := by sorry
