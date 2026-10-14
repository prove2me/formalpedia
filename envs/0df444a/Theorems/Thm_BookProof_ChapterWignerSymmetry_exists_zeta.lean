-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_exists_zeta
-- name    : BookProof.ChapterWignerSymmetry.exists_zeta
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:41:19.143482+00:00
-- url     : https://prove2.me/theorems/5958be46-803e-40db-ab7b-eb91e2846e96
-- title:
--   `BookProof.ChapterWignerSymmetry.exists_zeta` (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) : ∃ ζ : ℂ, (ζ = Complex.I ∨ ζ = -Complex.I) ∧ ∀ v, ‖conj (S v o) + ζ * conj (S v i)‖...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.exists_zeta` (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) : ∃ ζ : ℂ, (ζ = Complex.I ∨ ζ = -Complex.I) ∧ ∀ v, ‖conj (S v o) + ζ * conj (S v i)‖ = ‖conj (v o) + Complex.I * conj (v i)‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.exists_zeta`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.exists_zeta
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.exists_zeta (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) :
    ∃ ζ : ℂ, (ζ = Complex.I ∨ ζ = -Complex.I) ∧
      ∀ v, ‖conj (S v o) + ζ * conj (S v i)‖ = ‖conj (v o) + Complex.I * conj (v i)‖ := by sorry
