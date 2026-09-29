-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_sirk_limit_unique
-- name    : BookProof.YangMillsFriedrichsLimit.sirk_limit_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:48.25728+00:00
-- url     : https://prove2.me/theorems/26e13741-44ae-4a6d-a05e-6941f361f026
-- title:
--   The Lean 4 theorem `sirk_limit_unique` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_limit_unique` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.sirk_limit_unique
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped InnerProductSpace ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]







open BookProof.ChapterH5 BookProof.ChapterH9

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.sirk_limit_unique (A B : F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F) : Set F))
    (hagree : ∀ x ∈ (⨆ n : ℕ, krylovSpan A.toLinearMap v n : Submodule ℂ F), A x = B x) :
    A = B := by sorry
