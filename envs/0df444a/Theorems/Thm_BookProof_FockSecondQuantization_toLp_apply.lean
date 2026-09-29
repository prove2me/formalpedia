-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_toLp_apply
-- name    : BookProof.FockSecondQuantization.toLp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:24:53.558972+00:00
-- url     : https://prove2.me/theorems/bcaf4605-0f7d-4e8d-8a39-012f7fd6abc1
-- title:
--   (u : FockAlg) (α : Conf) : ((toLp u : Fock) : Conf → ℂ) α = u α
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.toLp_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.toLp_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.toLp_apply (u : FockAlg) (α : Conf) : ((toLp u : Fock) : Conf → ℂ) α = u α := by sorry
