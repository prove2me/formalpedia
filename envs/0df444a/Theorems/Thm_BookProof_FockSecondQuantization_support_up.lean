-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_support_up
-- name    : BookProof.FockSecondQuantization.support_up
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:00:02.248234+00:00
-- url     : https://prove2.me/theorems/530858bd-f486-4b3f-9b82-263f6635ab3e
-- title:
--   (j : ℕ) (α : Conf) : (up j α).support ⊆ insert j α.support
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.support_up` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.support_up
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.support_up (j : ℕ) (α : Conf) : (up j α).support ⊆ insert j α.support := by sorry
