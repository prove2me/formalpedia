-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp74_prop74_intertwine
-- name    : BookProof.ChapterMajoranaProp74.prop74_intertwine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:57:31.869296+00:00
-- url     : https://prove2.me/theorems/23b8486b-46be-4d8c-b662-5a7760d9afb7
-- title:
--   `BookProof.ChapterMajoranaProp74.prop74_intertwine` (g ns : Matrix (Fin 4) (Fin 4) ℂ) (hg2 : g * g = 1) (hns2 : ns * ns = -1) (hgns : g * ns = -(ns * g)) (c s m q E : ℝ) (hcs : c ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaProp74`.
--
--   `BookProof.ChapterMajoranaProp74.prop74_intertwine` (g ns : Matrix (Fin 4) (Fin 4) ℂ) (hg2 : g * g = 1) (hns2 : ns * ns = -1) (hgns : g * ns = -(ns * g)) (c s m q E : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hm : m = (c ^ 2 - s ^ 2) * E) (hq : q = 2 * c * s * E) : Qmat g ns m q * Sinv (ns * g) c s = Sinv (ns * g) c s * Rmat g E
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaProp74.prop74_intertwine`.

-- Generated from ChapterMajoranaProp74.lean — theorem BookProof.ChapterMajoranaProp74.prop74_intertwine
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
open BookProof.ChapterMajoranaProp74


open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaProp74.prop74_intertwine (g ns : Matrix (Fin 4) (Fin 4) ℂ)
    (hg2 : g * g = 1) (hns2 : ns * ns = -1) (hgns : g * ns = -(ns * g))
    (c s m q E : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hm : m = (c ^ 2 - s ^ 2) * E)
    (hq : q = 2 * c * s * E) :
    Qmat g ns m q * Sinv (ns * g) c s = Sinv (ns * g) c s * Rmat g E := by sorry
