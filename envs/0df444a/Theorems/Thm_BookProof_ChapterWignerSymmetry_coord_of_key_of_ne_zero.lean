-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_coord_of_key_of_ne_zero
-- name    : BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:36:45.112555+00:00
-- url     : https://prove2.me/theorems/93bd5875-8b39-456a-8248-d4a055ba46da
-- title:
--   `BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero` (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖) (hκc : ∀ z, κ (conj z) = conj (κ z)) (hkey : ∀ i,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero` (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖) (hκc : ∀ z, κ (conj z) = conj (κ z)) (hkey : ∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = κ (conj (v o) * v i)) {v : ι → ℂ} (hv : v o ≠ 0) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * κ (v k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.coord_of_key_of_ne_zero (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖)
    (hκc : ∀ z, κ (conj z) = conj (κ z))
    (hkey : ∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = κ (conj (v o) * v i))
    {v : ι → ℂ} (hv : v o ≠ 0) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * κ (v k) := by sorry
