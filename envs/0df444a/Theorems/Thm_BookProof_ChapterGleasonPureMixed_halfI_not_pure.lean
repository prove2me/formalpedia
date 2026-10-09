-- Prove2me | Theorems.Thm_BookProof_ChapterGleasonPureMixed_halfI_not_pure
-- name    : BookProof.ChapterGleasonPureMixed.halfI_not_pure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:55:39.130741+00:00
-- url     : https://prove2.me/theorems/0713652e-1999-4d1f-befb-87fc22266d5a
-- title:
--   `BookProof.ChapterGleasonPureMixed.halfI_not_pure` : ¬ IsPureState ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGleasonPureMixed`.
--
--   `BookProof.ChapterGleasonPureMixed.halfI_not_pure` : ¬ IsPureState ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGleasonPureMixed.halfI_not_pure`.

-- Generated from ChapterGleasonPureMixed.lean — theorem BookProof.ChapterGleasonPureMixed.halfI_not_pure
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
import Definitions.Def_ChapterB4
open BookProof.ChapterB4
open BookProof.ChapterGleasonPureMixed


open scoped BigOperators
open Matrix

theorem BookProof.ChapterGleasonPureMixed.halfI_not_pure :
    ¬ IsPureState ((1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by sorry
