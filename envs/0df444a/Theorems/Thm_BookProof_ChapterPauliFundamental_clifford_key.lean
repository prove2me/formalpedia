-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_clifford_key
-- name    : BookProof.ChapterPauliFundamental.clifford_key
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:29:23.728982+00:00
-- url     : https://prove2.me/theorems/aaa9d83c-225a-4d2f-8f9f-bc4a65f351e4
-- title:
--   `BookProof.ChapterPauliFundamental.clifford_key` (hA : IsCliffordC A) (μ : Fin 4) (T : Finset (Fin 4)) : A μ * gpF A T = sgnT μ T • gpF A (stepT μ T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.clifford_key` (hA : IsCliffordC A) (μ : Fin 4) (T : Finset (Fin 4)) : A μ * gpF A T = sgnT μ T • gpF A (stepT μ T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.clifford_key`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.clifford_key
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3b
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.clifford_key (hA : IsCliffordC A) (μ : Fin 4) (T : Finset (Fin 4)) :
    A μ * gpF A T = sgnT μ T • gpF A (stepT μ T) := by sorry
