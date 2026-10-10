-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_inter_intertwines
-- name    : BookProof.ChapterPauliFundamental.inter_intertwines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:29:54.303014+00:00
-- url     : https://prove2.me/theorems/2f0bd4b0-a12e-4882-bdfb-8c457e5721d8
-- title:
--   `BookProof.ChapterPauliFundamental.inter_intertwines` (hA : IsCliffordC A) (F : M4) (μ : Fin 4) : A μ * inter A F = inter A F * mgamma μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.inter_intertwines` (hA : IsCliffordC A) (F : M4) (μ : Fin 4) : A μ * inter A F = inter A F * mgamma μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.inter_intertwines`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.inter_intertwines
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

theorem BookProof.ChapterPauliFundamental.inter_intertwines (hA : IsCliffordC A) (F : M4) (μ : Fin 4) :
    A μ * inter A F = inter A F * mgamma μ := by sorry
