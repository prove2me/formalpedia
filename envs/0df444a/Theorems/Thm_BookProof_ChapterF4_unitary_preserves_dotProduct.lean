-- Prove2me | Theorems.Thm_BookProof_ChapterF4_unitary_preserves_dotProduct
-- name    : BookProof.ChapterF4.unitary_preserves_dotProduct
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:50:51.967046+00:00
-- url     : https://prove2.me/theorems/739b13a2-e55d-4029-985a-f8090e09364f
-- title:
--   `BookProof.ChapterF4.unitary_preserves_dotProduct` {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (x y : Fin n → ℂ) : star (U.mulVec x) ⬝ᵥ U.mulVec y = star x ⬝ᵥ y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.unitary_preserves_dotProduct` {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (x y : Fin n → ℂ) : star (U.mulVec x) ⬝ᵥ U.mulVec y = star x ⬝ᵥ y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.unitary_preserves_dotProduct`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.unitary_preserves_dotProduct
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}

theorem BookProof.ChapterF4.unitary_preserves_dotProduct {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (x y : Fin n → ℂ) :
    star (U.mulVec x) ⬝ᵥ U.mulVec y = star x ⬝ᵥ y := by sorry
