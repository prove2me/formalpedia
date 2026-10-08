-- Prove2me | Theorems.Thm_BookProof_ChapterA3_inv_of_sq_neg_one
-- name    : BookProof.ChapterA3.inv_of_sq_neg_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:37:35.794977+00:00
-- url     : https://prove2.me/theorems/2dc7b4d0-ce82-47d9-a724-1cb1f89198f1
-- title:
--   `BookProof.ChapterA3.inv_of_sq_neg_one` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) : S⁻¹ = -S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3d`.
--
--   `BookProof.ChapterA3.inv_of_sq_neg_one` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) : S⁻¹ = -S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.inv_of_sq_neg_one`.

-- Generated from ChapterA3d.lean — theorem BookProof.ChapterA3.inv_of_sq_neg_one
import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.inv_of_sq_neg_one {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) :
    S⁻¹ = -S := by sorry
