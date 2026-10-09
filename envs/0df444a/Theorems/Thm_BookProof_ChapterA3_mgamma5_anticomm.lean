-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma5_anticomm
-- name    : BookProof.ChapterA3.mgamma5_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:46:38.460083+00:00
-- url     : https://prove2.me/theorems/a25da6b0-9f2c-4af8-b28a-9040b3cba494
-- title:
--   `BookProof.ChapterA3.mgamma5_anticomm` (μ : Fin 4) : mgamma5 * mgamma μ + mgamma μ * mgamma5 = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3`.
--
--   `BookProof.ChapterA3.mgamma5_anticomm` (μ : Fin 4) : mgamma5 * mgamma μ + mgamma μ * mgamma5 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma5_anticomm`.

-- Generated from ChapterA3.lean — theorem BookProof.ChapterA3.mgamma5_anticomm
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma5_anticomm (μ : Fin 4) :
    mgamma5 * mgamma μ + mgamma μ * mgamma5 = 0 := by sorry
