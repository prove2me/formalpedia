-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_dslit_weakValue
-- name    : BookProof.ChapterWeakValue.dslit_weakValue
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:46.625016+00:00
-- url     : https://prove2.me/theorems/362e1eff-4147-45d2-b788-d630d76e6c98
-- title:
--   `BookProof.ChapterWeakValue.dslit_weakValue` : weakValue (H *ᵥ psi0) psi0 (projMat 0) = 1 ∧ weakValue (H *ᵥ psi0) psi0 (projMat 1) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.dslit_weakValue` : weakValue (H *ᵥ psi0) psi0 (projMat 0) = 1 ∧ weakValue (H *ᵥ psi0) psi0 (projMat 1) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.dslit_weakValue`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.dslit_weakValue
import Mathlib
import Definitions.Def_ChapterWeakValue
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.dslit_weakValue :
    weakValue (H *ᵥ psi0) psi0 (projMat 0) = 1 ∧
      weakValue (H *ᵥ psi0) psi0 (projMat 1) = 0 := by sorry
