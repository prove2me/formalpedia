-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_coord_of_key
-- name    : BookProof.ChapterWignerSymmetry.coord_of_key
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:34:25.449596+00:00
-- url     : https://prove2.me/theorems/84b3fe77-9a3b-425e-b5d5-3fda614c7133
-- title:
--   `BookProof.ChapterWignerSymmetry.coord_of_key` (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖) (hκc : ∀ z, κ (conj z) = conj (κ z)) (hkey : ∀ i, i ≠ o...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.coord_of_key` (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖) (hκc : ∀ z, κ (conj z) = conj (κ z)) (hkey : ∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = κ (conj (v o) * v i)) (v : ι → ℂ) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * κ (v k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.coord_of_key`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.coord_of_key
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.coord_of_key (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖)
    (hκc : ∀ z, κ (conj z) = conj (κ z))
    (hkey : ∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = κ (conj (v o) * v i)) (v : ι → ℂ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * κ (v k) := by sorry
