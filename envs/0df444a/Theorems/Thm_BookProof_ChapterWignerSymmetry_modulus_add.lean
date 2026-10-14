-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_modulus_add
-- name    : BookProof.ChapterWignerSymmetry.modulus_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:42:04.647661+00:00
-- url     : https://prove2.me/theorems/d6154977-3ffa-4ab1-a82e-769e757e3c21
-- title:
--   `BookProof.ChapterWignerSymmetry.modulus_add` (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) (v : ι → ℂ) : ‖S v o + S v i‖ = ‖v o + v i‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.modulus_add` (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) (v : ι → ℂ) : ‖S v o + S v i‖ = ‖v o + v i‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.modulus_add`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.modulus_add
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.modulus_add (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) (v : ι → ℂ) :
    ‖S v o + S v i‖ = ‖v o + v i‖ := by sorry
