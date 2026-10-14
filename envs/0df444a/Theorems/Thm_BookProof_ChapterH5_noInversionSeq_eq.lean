-- Prove2me | Theorems.Thm_BookProof_ChapterH5_noInversionSeq_eq
-- name    : BookProof.ChapterH5.noInversionSeq_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:48:03.194815+00:00
-- url     : https://prove2.me/theorems/65cd64bb-64ae-4db0-bdd8-e7f93f1b13d8
-- title:
--   `BookProof.ChapterH5.noInversionSeq_eq` (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) : noInversionSeq H γ v k = (((H - γ • 1) ^ k) v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.noInversionSeq_eq` (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) : noInversionSeq H γ v k = (((H - γ • 1) ^ k) v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.noInversionSeq_eq`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.noInversionSeq_eq
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.noInversionSeq_eq (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) :
    noInversionSeq H γ v k = (((H - γ • 1) ^ k) v) := by sorry
