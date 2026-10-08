-- Prove2me | Theorems.Thm_BookProof_ChapterE3_eulerJ_antisymm
-- name    : BookProof.ChapterE3.eulerJ_antisymm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:12:35.074418+00:00
-- url     : https://prove2.me/theorems/eb4d990f-fc10-4e8c-b4df-6f9c8034703b
-- title:
--   `BookProof.ChapterE3.eulerJ_antisymm` (l w : Fin n → ℝ) : (eulerJ l w)ᵀ = - eulerJ l w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE3`.
--
--   `BookProof.ChapterE3.eulerJ_antisymm` (l w : Fin n → ℝ) : (eulerJ l w)ᵀ = - eulerJ l w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE3.eulerJ_antisymm`.

-- Generated from ChapterE3.lean — theorem BookProof.ChapterE3.eulerJ_antisymm
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3


open scoped Matrix BigOperators


variable {n : ℕ}

theorem BookProof.ChapterE3.eulerJ_antisymm (l w : Fin n → ℝ) :
    (eulerJ l w)ᵀ = - eulerJ l w := by sorry
