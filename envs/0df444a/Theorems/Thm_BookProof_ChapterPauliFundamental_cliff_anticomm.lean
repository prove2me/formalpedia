-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_cliff_anticomm
-- name    : BookProof.ChapterPauliFundamental.cliff_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:07.888326+00:00
-- url     : https://prove2.me/theorems/9abc8ef4-eeb9-4e4d-b9bd-77dd47e39b6f
-- title:
--   `BookProof.ChapterPauliFundamental.cliff_anticomm` (hA : IsCliffordC A) {μ ν : Fin 4} (h : μ ≠ ν) : A μ * A ν = -(A ν * A μ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.cliff_anticomm` (hA : IsCliffordC A) {μ ν : Fin 4} (h : μ ≠ ν) : A μ * A ν = -(A ν * A μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.cliff_anticomm`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.cliff_anticomm
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.cliff_anticomm (hA : IsCliffordC A) {μ ν : Fin 4} (h : μ ≠ ν) :
    A μ * A ν = -(A ν * A μ) := by sorry
