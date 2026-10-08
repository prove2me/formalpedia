-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_SUtwo_mul_conjTranspose
-- name    : BookProof.ChapterA4g.SUtwo_mul_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:44:02.981603+00:00
-- url     : https://prove2.me/theorems/0cc6ac2e-6d4f-46e9-8a6b-4c671528ec24
-- title:
--   `BookProof.ChapterA4g.SUtwo_mul_conjTranspose` {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SUtwo) : S * Sᴴ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.SUtwo_mul_conjTranspose` {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SUtwo) : S * Sᴴ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.SUtwo_mul_conjTranspose`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SUtwo_mul_conjTranspose
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4c
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.SUtwo_mul_conjTranspose {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SUtwo) : S * Sᴴ = 1 := by sorry
