-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_hadamard_psi0
-- name    : BookProof.ChapterWeakValue.hadamard_psi0
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:29.902984+00:00
-- url     : https://prove2.me/theorems/7974f978-352c-41d2-bfa3-9b746d5e5d7a
-- title:
--   `BookProof.ChapterWeakValue.hadamard_psi0` : (H *ᵥ psi0) = ![(1 / Real.sqrt 2 : ℂ), (1 / Real.sqrt 2 : ℂ)]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.hadamard_psi0` : (H *ᵥ psi0) = ![(1 / Real.sqrt 2 : ℂ), (1 / Real.sqrt 2 : ℂ)]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.hadamard_psi0`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.hadamard_psi0
import Mathlib
import Definitions.Def_ChapterWeakValue
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.hadamard_psi0 : (H *ᵥ psi0) = ![(1 / Real.sqrt 2 : ℂ), (1 / Real.sqrt 2 : ℂ)] := by sorry
