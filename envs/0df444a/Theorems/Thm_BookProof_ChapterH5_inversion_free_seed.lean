-- Prove2me | Theorems.Thm_BookProof_ChapterH5_inversion_free_seed
-- name    : BookProof.ChapterH5.inversion_free_seed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:47:07.986464+00:00
-- url     : https://prove2.me/theorems/480029f5-2e79-4573-bbc9-b0ee740dc12e
-- title:
--   `BookProof.ChapterH5.inversion_free_seed` (S R : E →ₗ[K] E) (v₀ : E) (m : ℕ) (hR : R.comp S = LinearMap.id) : R ((S ^ (m + 1)) v₀) = (S ^ m) v₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.inversion_free_seed` (S R : E →ₗ[K] E) (v₀ : E) (m : ℕ) (hR : R.comp S = LinearMap.id) : R ((S ^ (m + 1)) v₀) = (S ^ m) v₀
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.inversion_free_seed`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.inversion_free_seed
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.inversion_free_seed (S R : E →ₗ[K] E) (v₀ : E) (m : ℕ)
    (hR : R.comp S = LinearMap.id) :
    R ((S ^ (m + 1)) v₀) = (S ^ m) v₀ := by sorry
