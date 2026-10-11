-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_key_consistent
-- name    : BookProof.ChapterWignerSymmetry.key_consistent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:34:11.402569+00:00
-- url     : https://prove2.me/theorems/8745b49e-3115-49df-ac31-3ce957d74e69
-- title:
--   `BookProof.ChapterWignerSymmetry.key_consistent` (hS : WignerCoord S o) {i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j) (hi : ∀ v, conj (S v o) * S v i = conj (v o) * v i) (hj
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.key_consistent` (hS : WignerCoord S o) {i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j) (hi : ∀ v, conj (S v o) * S v i = conj (v o) * v i) (hj : ∀ v, conj (S v o) * S v j = conj (conj (v o) * v j)) : False
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.key_consistent`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.key_consistent
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.key_consistent (hS : WignerCoord S o) {i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j)
    (hi : ∀ v, conj (S v o) * S v i = conj (v o) * v i)
    (hj : ∀ v, conj (S v o) * S v j = conj (conj (v o) * v j)) : False := by sorry
