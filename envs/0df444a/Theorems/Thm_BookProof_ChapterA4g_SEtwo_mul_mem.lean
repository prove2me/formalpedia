-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_SEtwo_mul_mem
-- name    : BookProof.ChapterA4g.SEtwo_mul_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:44:38.864267+00:00
-- url     : https://prove2.me/theorems/8ee19d23-0713-4fdb-8c56-249737faa008
-- title:
--   `BookProof.ChapterA4g.SEtwo_mul_mem` {S T : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SEtwo) (hT : T ∈ SEtwo) : S * T ∈ SEtwo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.SEtwo_mul_mem` {S T : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SEtwo) (hT : T ∈ SEtwo) : S * T ∈ SEtwo
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.SEtwo_mul_mem`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SEtwo_mul_mem
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4d
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.SEtwo_mul_mem {S T : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SEtwo) (hT : T ∈ SEtwo) : S * T ∈ SEtwo := by sorry
