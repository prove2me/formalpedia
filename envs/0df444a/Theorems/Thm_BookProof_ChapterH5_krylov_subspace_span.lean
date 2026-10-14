-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylov_subspace_span
-- name    : BookProof.ChapterH5.krylov_subspace_span
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:46:37.308029+00:00
-- url     : https://prove2.me/theorems/855d418c-f33b-48b6-aa2c-953b815b2552
-- title:
--   `BookProof.ChapterH5.krylov_subspace_span` (H : E →ₗ[K] E) (v : E) (m : ℕ) : krylovSpan H v m = Submodule.span K {x | ∃ i < m, x = (H ^ i) v}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylov_subspace_span` (H : E →ₗ[K] E) (v : E) (m : ℕ) : krylovSpan H v m = Submodule.span K {x | ∃ i < m, x = (H ^ i) v}
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylov_subspace_span`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylov_subspace_span
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylov_subspace_span (H : E →ₗ[K] E) (v : E) (m : ℕ) :
    krylovSpan H v m = Submodule.span K {x | ∃ i < m, x = (H ^ i) v} := by sorry
