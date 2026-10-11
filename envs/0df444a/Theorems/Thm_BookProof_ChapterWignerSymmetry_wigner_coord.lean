-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_wigner_coord
-- name    : BookProof.ChapterWignerSymmetry.wigner_coord
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:18:14.428978+00:00
-- url     : https://prove2.me/theorems/75b79c15-5995-424c-8a0f-5b3b4548be48
-- title:
--   `BookProof.ChapterWignerSymmetry.wigner_coord` (hS : WignerCoord S o) : (∀ v, ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * v k) ∨ (∀ v, ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.wigner_coord` (hS : WignerCoord S o) : (∀ v, ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * v k) ∨ (∀ v, ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * conj (v k))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.wigner_coord`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.wigner_coord
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.wigner_coord (hS : WignerCoord S o) :
    (∀ v, ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * v k) ∨
    (∀ v, ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * conj (v k)) := by sorry
