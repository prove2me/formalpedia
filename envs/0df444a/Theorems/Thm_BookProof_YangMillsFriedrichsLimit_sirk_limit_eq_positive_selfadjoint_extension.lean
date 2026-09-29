-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_sirk_limit_eq_positive_selfadjoint_extension
-- name    : BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:02.696854+00:00
-- url     : https://prove2.me/theorems/df0bdf05-5b1c-401e-b9c2-6c5acd2db3ae
-- title:
--   The Lean 4 theorem `sirk_limit_eq_positive_selfadjoint_extension` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_limit_eq_positive_selfadjoint_extension` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension [CompleteSpace F] {D : Submodule ℂ F}
    (H : D →ₗ[ℂ] F) (hdenseD : Dense (D : Set F)) (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) (C : ℝ) (hbd : ∀ x : D, ‖H x‖ ≤ C * ‖(x : F)‖) (v : F) :
    ∃ A : F →L[ℂ] F,
      (∀ x : D, A (x : F) = H x) ∧
      IsPositiveSelfAdjointExtension H (topRestrict A) ∧
      (Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F) →
        (∀ u : F, Filter.Tendsto (fun n : ℕ => sirkCompression A v n u)
          Filter.atTop (nhds (A u)))
        ∧ ∀ B : F →L[ℂ] F,
            (∀ x ∈ (⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F), A x = B x) →
            A = B) := by sorry
