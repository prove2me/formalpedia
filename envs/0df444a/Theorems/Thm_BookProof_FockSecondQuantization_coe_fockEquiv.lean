-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv
-- name    : BookProof.FockSecondQuantization.coe_fockEquiv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:15:29.930417+00:00
-- url     : https://prove2.me/theorems/9c09a4d9-7de8-40fd-8d08-0e3dd6c03341
-- title:
--   (u : FockAlg) : ((fockEquiv u : lpFiniteModes Conf) : Fock) = toLp u
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.coe_fockEquiv` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.coe_fockEquiv
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.coe_fockEquiv (u : FockAlg) : ((fockEquiv u : lpFiniteModes Conf) : Fock)
    = toLp u := by sorry
