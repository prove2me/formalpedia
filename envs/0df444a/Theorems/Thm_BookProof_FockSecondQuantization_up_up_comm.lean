-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_up_up_comm
-- name    : BookProof.FockSecondQuantization.up_up_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:02:48.819918+00:00
-- url     : https://prove2.me/theorems/c9c066ac-2b55-4c48-9b69-541110b2a7af
-- title:
--   (j k : ℕ) (α : Conf) : up k (up j α) = up j (up k α)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.up_up_comm` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.up_up_comm
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.up_up_comm (j k : ℕ) (α : Conf) : up k (up j α) = up j (up k α) := by sorry
