-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_positive_sqrt_unique
-- name    : BookProof.ClosureUniqueness.positive_sqrt_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:43:54.143603+00:00
-- url     : https://prove2.me/theorems/67bde467-4eee-4f93-8090-cf33be5bdb1f
-- title:
--   `BookProof.ClosureUniqueness.positive_sqrt_unique` {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S B C : H →L[ℂ] H) (hB : B.IsPositive) (hC : C.IsPo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.positive_sqrt_unique` {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S B C : H →L[ℂ] H) (hB : B.IsPositive) (hC : C.IsPositive) (hBS : B ∘L B = S) (hCS : C ∘L C = S) : B = C
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.positive_sqrt_unique`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.positive_sqrt_unique
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.ClosureUniqueness.positive_sqrt_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S B C : H →L[ℂ] H) (hB : B.IsPositive) (hC : C.IsPositive)
    (hBS : B ∘L B = S) (hCS : C ∘L C = S) : B = C := by sorry
