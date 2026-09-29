-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_up_injective
-- name    : BookProof.FockSecondQuantization.up_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:59:08.118534+00:00
-- url     : https://prove2.me/theorems/0d6dc6cb-cfb6-4053-9d12-7716034502a8
-- title:
--   (j : ℕ) : Function.Injective (up j)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.up_injective` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.up_injective
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.up_injective (j : ℕ) : Function.Injective (up j) := by sorry
