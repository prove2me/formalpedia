-- Prove2me | Theorems.Thm_BookProof_ChapterPinDoubleCover_LamZ_hom
-- name    : BookProof.ChapterPinDoubleCover.LamZ_hom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:51:50.925618+00:00
-- url     : https://prove2.me/theorems/1e57ba55-54b3-4708-9e3a-01ca96c99266
-- title:
--   `BookProof.ChapterPinDoubleCover.LamZ_hom` : ∀ S ∈ Omega, ∀ T ∈ Omega, LamZ (S * T) = LamZ S * LamZ T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPinDoubleCover`.
--
--   `BookProof.ChapterPinDoubleCover.LamZ_hom` : ∀ S ∈ Omega, ∀ T ∈ Omega, LamZ (S * T) = LamZ S * LamZ T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPinDoubleCover.LamZ_hom`.

-- Generated from ChapterPinDoubleCover.lean — theorem BookProof.ChapterPinDoubleCover.LamZ_hom
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinDoubleCover


open Matrix


open BookProof.ChapterA3
open Classical

theorem BookProof.ChapterPinDoubleCover.LamZ_hom : ∀ S ∈ Omega, ∀ T ∈ Omega, LamZ (S * T) = LamZ S * LamZ T := by sorry
