-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_hasSum_sq_samples
-- name    : BookProof.ChapterShannonSampling.hasSum_sq_samples
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:24:20.093194+00:00
-- url     : https://prove2.me/theorems/4d0650ff-f7c6-4075-a60f-26ecad232525
-- title:
--   `BookProof.ChapterShannonSampling.hasSum_sq_samples` (F : Lp ℂ 2 (haarAddCircle (T := T))) : HasSum (fun n : ℤ => ‖bandSignal (T := T) (F : AddCircle T → ℂ) (n / T)‖ ^ 2) (T * ∫ ξ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.hasSum_sq_samples` (F : Lp ℂ 2 (haarAddCircle (T := T))) : HasSum (fun n : ℤ => ‖bandSignal (T := T) (F : AddCircle T → ℂ) (n / T)‖ ^ 2) (T * ∫ ξ in (-(T / 2))..(-(T / 2) + T), ‖(F : AddCircle T → ℂ) ξ‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.hasSum_sq_samples`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.hasSum_sq_samples
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.hasSum_sq_samples (F : Lp ℂ 2 (haarAddCircle (T := T))) :
    HasSum (fun n : ℤ => ‖bandSignal (T := T) (F : AddCircle T → ℂ) (n / T)‖ ^ 2)
      (T * ∫ ξ in (-(T / 2))..(-(T / 2) + T), ‖(F : AddCircle T → ℂ) ξ‖ ^ 2) := by sorry
