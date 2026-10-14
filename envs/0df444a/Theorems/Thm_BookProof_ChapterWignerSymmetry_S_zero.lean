-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_S_zero
-- name    : BookProof.ChapterWignerSymmetry.S_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:41:01.314557+00:00
-- url     : https://prove2.me/theorems/dfaba3a1-fda4-435b-ae21-fa08068df3f6
-- title:
--   `BookProof.ChapterWignerSymmetry.S_zero` (hS : WignerCoord S o) {v : ι → ℂ} {k : ι} (h : v k = 0) : S v k = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.S_zero` (hS : WignerCoord S o) {v : ι → ℂ} {k : ι} (h : v k = 0) : S v k = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.S_zero`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.S_zero
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.S_zero (hS : WignerCoord S o) {v : ι → ℂ} {k : ι} (h : v k = 0) : S v k = 0 := by sorry
