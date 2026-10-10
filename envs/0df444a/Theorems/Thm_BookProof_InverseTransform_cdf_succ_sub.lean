-- Prove2me | Theorems.Thm_BookProof_InverseTransform_cdf_succ_sub
-- name    : BookProof.InverseTransform.cdf_succ_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:16:49.927803+00:00
-- url     : https://prove2.me/theorems/247ee846-3ba3-40b8-9e2b-6ec28c22e8b3
-- title:
--   `BookProof.InverseTransform.cdf_succ_sub` (k : ℕ) : cdf p (k + 1) - cdf p k = p k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterInverseTransform`.
--
--   `BookProof.InverseTransform.cdf_succ_sub` (k : ℕ) : cdf p (k + 1) - cdf p k = p k
--
--   Formalization note: Lean 4 identifier `BookProof.InverseTransform.cdf_succ_sub`.

-- Generated from ChapterInverseTransform.lean — theorem BookProof.InverseTransform.cdf_succ_sub
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform



open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

theorem BookProof.InverseTransform.cdf_succ_sub (k : ℕ) : cdf p (k + 1) - cdf p k = p k := by sorry
