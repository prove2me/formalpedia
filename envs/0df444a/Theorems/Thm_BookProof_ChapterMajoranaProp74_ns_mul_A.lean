-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp74_ns_mul_A
-- name    : BookProof.ChapterMajoranaProp74.ns_mul_A
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:57:17.682+00:00
-- url     : https://prove2.me/theorems/c63a53d8-c141-45dd-9a7f-8a36dff16270
-- title:
--   `BookProof.ChapterMajoranaProp74.ns_mul_A` {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hns2 : ns * ns = -1) : ns * (ns * g) = -g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaProp74`.
--
--   `BookProof.ChapterMajoranaProp74.ns_mul_A` {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hns2 : ns * ns = -1) : ns * (ns * g) = -g
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaProp74.ns_mul_A`.

-- Generated from ChapterMajoranaProp74.lean — theorem BookProof.ChapterMajoranaProp74.ns_mul_A
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
open BookProof.ChapterMajoranaProp74


open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaProp74.ns_mul_A {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hns2 : ns * ns = -1) :
    ns * (ns * g) = -g := by sorry
