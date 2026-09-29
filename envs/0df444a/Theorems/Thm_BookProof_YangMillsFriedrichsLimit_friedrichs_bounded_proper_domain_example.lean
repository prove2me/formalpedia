-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_friedrichs_bounded_proper_domain_example
-- name    : BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_proper_domain_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:04.23848+00:00
-- url     : https://prove2.me/theorems/5a17901f-810e-4751-a257-7c0eb82d2517
-- title:
--   The Lean 4 theorem `friedrichs_bounded_proper_domain_example` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `friedrichs_bounded_proper_domain_example` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_proper_domain_example
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open scoped ENNReal InnerProductSpace lp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_proper_domain_example :
    ∃ (D : Submodule ℂ (ℓ²(ℕ, ℂ))) (A : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)),
      Dense (D : Set (ℓ²(ℕ, ℂ))) ∧ D ≠ ⊤ ∧
      (∀ x : D, A (x : ℓ²(ℕ, ℂ)) = D.subtype x) ∧
      IsPositiveSelfAdjointExtension D.subtype (topRestrict A) := by sorry
