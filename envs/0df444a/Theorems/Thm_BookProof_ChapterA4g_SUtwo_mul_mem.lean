-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_SUtwo_mul_mem
-- name    : BookProof.ChapterA4g.SUtwo_mul_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:44:24.086985+00:00
-- url     : https://prove2.me/theorems/e07cdbec-11e6-4212-b475-3da4da51960f
-- title:
--   `BookProof.ChapterA4g.SUtwo_mul_mem` {S T : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SUtwo) (hT : T ∈ SUtwo) : S * T ∈ SUtwo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.SUtwo_mul_mem` {S T : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SUtwo) (hT : T ∈ SUtwo) : S * T ∈ SUtwo
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.SUtwo_mul_mem`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SUtwo_mul_mem
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4c
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.SUtwo_mul_mem {S T : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SUtwo) (hT : T ∈ SUtwo) : S * T ∈ SUtwo := by sorry
