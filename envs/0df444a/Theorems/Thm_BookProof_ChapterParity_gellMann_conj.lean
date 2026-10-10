-- Prove2me | Theorems.Thm_BookProof_ChapterParity_gellMann_conj
-- name    : BookProof.ChapterParity.gellMann_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:05:21.695574+00:00
-- url     : https://prove2.me/theorems/fdf66a5e-a9fa-4b1c-8a01-4b66e6b52f64
-- title:
--   `BookProof.ChapterParity.gellMann_conj` (a : Fin 8) : (gellMann a).map (starRingEnd ℂ) = (gellMannConjSign a) • gellMann a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParity`.
--
--   `BookProof.ChapterParity.gellMann_conj` (a : Fin 8) : (gellMann a).map (starRingEnd ℂ) = (gellMannConjSign a) • gellMann a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParity.gellMann_conj`.

-- Generated from ChapterParity.lean — theorem BookProof.ChapterParity.gellMann_conj
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity


open Matrix
open scoped ComplexConjugate

variable {n : Type*}

theorem BookProof.ChapterParity.gellMann_conj (a : Fin 8) :
    (gellMann a).map (starRingEnd ℂ) = (gellMannConjSign a) • gellMann a := by sorry
