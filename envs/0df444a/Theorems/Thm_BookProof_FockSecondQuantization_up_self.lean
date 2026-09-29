-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_up_self
-- name    : BookProof.FockSecondQuantization.up_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:26:56.761089+00:00
-- url     : https://prove2.me/theorems/21cc7e8d-bc4e-4c12-a468-be21744008d9
-- title:
--   (j : ℕ) (α : Conf) : up j α j = α j + 1
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.up_self` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.up_self
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.up_self (j : ℕ) (α : Conf) : up j α j = α j + 1 := by sorry
