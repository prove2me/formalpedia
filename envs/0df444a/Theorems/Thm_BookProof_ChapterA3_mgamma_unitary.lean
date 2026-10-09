-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_unitary
-- name    : BookProof.ChapterA3.mgamma_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:41:34.625984+00:00
-- url     : https://prove2.me/theorems/71aa8cda-0355-4bde-bfee-fa20e6a7eff3
-- title:
--   `BookProof.ChapterA3.mgamma_unitary` (μ : Fin 4) : (mgamma μ)ᴴ * mgamma μ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3`.
--
--   `BookProof.ChapterA3.mgamma_unitary` (μ : Fin 4) : (mgamma μ)ᴴ * mgamma μ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_unitary`.

-- Generated from ChapterA3.lean — theorem BookProof.ChapterA3.mgamma_unitary
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_unitary (μ : Fin 4) :
    (mgamma μ)ᴴ * mgamma μ = 1 := by sorry
