-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp74_g_mul_A
-- name    : BookProof.ChapterMajoranaProp74.g_mul_A
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:57:07.387863+00:00
-- url     : https://prove2.me/theorems/13852933-5595-4957-9211-5834b635ebe2
-- title:
--   `BookProof.ChapterMajoranaProp74.g_mul_A` {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hg2 : g * g = 1) (hgns : g * ns = -(ns * g)) : g * (ns * g) = -ns
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaProp74`.
--
--   `BookProof.ChapterMajoranaProp74.g_mul_A` {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hg2 : g * g = 1) (hgns : g * ns = -(ns * g)) : g * (ns * g) = -ns
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaProp74.g_mul_A`.

-- Generated from ChapterMajoranaProp74.lean — theorem BookProof.ChapterMajoranaProp74.g_mul_A
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
open BookProof.ChapterMajoranaProp74


open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaProp74.g_mul_A {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hg2 : g * g = 1)
    (hgns : g * ns = -(ns * g)) : g * (ns * g) = -ns := by sorry
