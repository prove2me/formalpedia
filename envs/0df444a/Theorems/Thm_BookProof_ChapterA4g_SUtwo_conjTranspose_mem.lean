-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_SUtwo_conjTranspose_mem
-- name    : BookProof.ChapterA4g.SUtwo_conjTranspose_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:44:17.481977+00:00
-- url     : https://prove2.me/theorems/5668aa35-8288-4936-a345-9f208ffec2da
-- title:
--   `BookProof.ChapterA4g.SUtwo_conjTranspose_mem` {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SUtwo) : Sᴴ ∈ SUtwo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.SUtwo_conjTranspose_mem` {S : Matrix (Fin 2) (Fin 2) ℂ} (hS : S ∈ SUtwo) : Sᴴ ∈ SUtwo
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.SUtwo_conjTranspose_mem`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.SUtwo_conjTranspose_mem
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4c
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.SUtwo_conjTranspose_mem {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ SUtwo) : Sᴴ ∈ SUtwo := by sorry
