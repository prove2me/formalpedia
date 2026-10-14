-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylov_no_inversion_eq_standard
-- name    : BookProof.ChapterH5.krylov_no_inversion_eq_standard
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:47:31.368204+00:00
-- url     : https://prove2.me/theorems/dae7b7ee-ea4e-44a6-9061-62b747c8e474
-- title:
--   `BookProof.ChapterH5.krylov_no_inversion_eq_standard` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : Submodule.span K {x | ∃ i < m, x = noInversionSeq H γ v i} = krylovSpan H v m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylov_no_inversion_eq_standard` (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) : Submodule.span K {x | ∃ i < m, x = noInversionSeq H γ v i} = krylovSpan H v m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylov_no_inversion_eq_standard`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylov_no_inversion_eq_standard
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylov_no_inversion_eq_standard (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = noInversionSeq H γ v i} = krylovSpan H v m := by sorry
