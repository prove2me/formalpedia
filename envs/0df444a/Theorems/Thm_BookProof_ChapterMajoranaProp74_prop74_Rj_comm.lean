-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp74_prop74_Rj_comm
-- name    : BookProof.ChapterMajoranaProp74.prop74_Rj_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:57:23.638723+00:00
-- url     : https://prove2.me/theorems/aa183267-70ad-45b2-8f7d-4b468a348a99
-- title:
--   `BookProof.ChapterMajoranaProp74.prop74_Rj_comm` (g ns : Matrix (Fin 4) (Fin 4) ℂ) (_hg2 : g * g = 1) (hgns : g * ns = -(ns * g)) (c s pj : ℝ) : Dmat g pj * Sinv (ns * g) c s = Sin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaProp74`.
--
--   `BookProof.ChapterMajoranaProp74.prop74_Rj_comm` (g ns : Matrix (Fin 4) (Fin 4) ℂ) (_hg2 : g * g = 1) (hgns : g * ns = -(ns * g)) (c s pj : ℝ) : Dmat g pj * Sinv (ns * g) c s = Sinv (ns * g) c s * Dmat g pj
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaProp74.prop74_Rj_comm`.

-- Generated from ChapterMajoranaProp74.lean — theorem BookProof.ChapterMajoranaProp74.prop74_Rj_comm
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
open BookProof.ChapterMajoranaProp74


open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaProp74.prop74_Rj_comm (g ns : Matrix (Fin 4) (Fin 4) ℂ)
    (_hg2 : g * g = 1) (hgns : g * ns = -(ns * g)) (c s pj : ℝ) :
    Dmat g pj * Sinv (ns * g) c s = Sinv (ns * g) c s * Dmat g pj := by sorry
