-- Prove2me | Theorems.Thm_BookProof_ChapterDoubleSlit_slit_closed_born
-- name    : BookProof.ChapterDoubleSlit.slit_closed_born
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:07:16.180766+00:00
-- url     : https://prove2.me/theorems/9bf384d2-798f-4e8d-b49d-a0301dbb2ac8
-- title:
--   `BookProof.ChapterDoubleSlit.slit_closed_born` (i : Fin 2) : bornProb (H *ᵥ psi0) i = 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDoubleSlit`.
--
--   `BookProof.ChapterDoubleSlit.slit_closed_born` (i : Fin 2) : bornProb (H *ᵥ psi0) i = 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDoubleSlit.slit_closed_born`.

-- Generated from ChapterDoubleSlit.lean — theorem BookProof.ChapterDoubleSlit.slit_closed_born
import Mathlib
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit


open Matrix
open scoped BigOperators

theorem BookProof.ChapterDoubleSlit.slit_closed_born (i : Fin 2) : bornProb (H *ᵥ psi0) i = 1 / 2 := by sorry
