-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_key_index
-- name    : BookProof.ChapterWignerSymmetry.key_index
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:34:12.63944+00:00
-- url     : https://prove2.me/theorems/906c9700-92e3-4d90-8b14-b442c613b4af
-- title:
--   `BookProof.ChapterWignerSymmetry.key_index` (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) : (∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨ (∀ v, conj (S v o) * S v i = conj (conj (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.key_index` (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) : (∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨ (∀ v, conj (S v o) * S v i = conj (conj (v o) * v i))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.key_index`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.key_index
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.key_index (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) :
    (∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨
    (∀ v, conj (S v o) * S v i = conj (conj (v o) * v i)) := by sorry
