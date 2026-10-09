-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_tensorPow_mul
-- name    : BookProof.ChapterA3n.tensorPow_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:19.078337+00:00
-- url     : https://prove2.me/theorems/64b18afb-22d1-46de-b984-267a32474078
-- title:
--   `BookProof.ChapterA3n.tensorPow_mul` {N : ℕ} (M M' : Fin N → Matrix (Fin 4) (Fin 4) ℂ) : tensorPow M * tensorPow M' = tensorPow (fun i => M i * M' i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.tensorPow_mul` {N : ℕ} (M M' : Fin N → Matrix (Fin 4) (Fin 4) ℂ) : tensorPow M * tensorPow M' = tensorPow (fun i => M i * M' i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.tensorPow_mul`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.tensorPow_mul
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.tensorPow_mul {N : ℕ} (M M' : Fin N → Matrix (Fin 4) (Fin 4) ℂ) :
    tensorPow M * tensorPow M' = tensorPow (fun i => M i * M' i) := by sorry
