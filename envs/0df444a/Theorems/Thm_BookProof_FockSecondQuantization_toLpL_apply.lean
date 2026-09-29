-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_toLpL_apply
-- name    : BookProof.FockSecondQuantization.toLpL_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:24:11.536566+00:00
-- url     : https://prove2.me/theorems/4bea653e-b98c-4fcf-8595-080ff94131f4
-- title:
--   (u : FockAlg) : toLpL u = toLp u
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.toLpL_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.toLpL_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.toLpL_apply (u : FockAlg) : toLpL u = toLp u := by sorry
