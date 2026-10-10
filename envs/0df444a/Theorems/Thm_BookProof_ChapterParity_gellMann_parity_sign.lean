-- Prove2me | Theorems.Thm_BookProof_ChapterParity_gellMann_parity_sign
-- name    : BookProof.ChapterParity.gellMann_parity_sign
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:05:24.445983+00:00
-- url     : https://prove2.me/theorems/936c211c-00ff-4250-a926-8d2d6a813c85
-- title:
--   `BookProof.ChapterParity.gellMann_parity_sign` (a : Fin 8) : -((gellMann a).map (starRingEnd ℂ)) = (-(gellMannConjSign a)) • gellMann a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParity`.
--
--   `BookProof.ChapterParity.gellMann_parity_sign` (a : Fin 8) : -((gellMann a).map (starRingEnd ℂ)) = (-(gellMannConjSign a)) • gellMann a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParity.gellMann_parity_sign`.

-- Generated from ChapterParity.lean — theorem BookProof.ChapterParity.gellMann_parity_sign
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity


open Matrix
open scoped ComplexConjugate

variable {n : Type*}

theorem BookProof.ChapterParity.gellMann_parity_sign (a : Fin 8) :
    -((gellMann a).map (starRingEnd ℂ)) = (-(gellMannConjSign a)) • gellMann a := by sorry
