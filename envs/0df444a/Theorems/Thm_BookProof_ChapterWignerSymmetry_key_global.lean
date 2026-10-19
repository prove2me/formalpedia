-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_key_global
-- name    : BookProof.ChapterWignerSymmetry.key_global
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:50.150738+00:00
-- url     : https://prove2.me/theorems/a746fc83-4231-4812-bfbf-5b4fd98d15f6
-- title:
--   `BookProof.ChapterWignerSymmetry.key_global` (hS : WignerCoord S o) : (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨ (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.key_global` (hS : WignerCoord S o) : (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨ (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (conj (v o) * v i))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.key_global`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.key_global
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.key_global (hS : WignerCoord S o) :
    (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (v o) * v i) ∨
    (∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = conj (conj (v o) * v i)) := by sorry
