-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
-- name    : BookProof.FockSecondQuantization.coe_fockEquiv_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:56:20.634113+00:00
-- url     : https://prove2.me/theorems/33d60650-34a0-49de-a837-34bb8f08367e
-- title:
--   (x : lpFiniteModes Conf) : ((x : lpFiniteModes Conf) : Fock) = toLp (fockEquiv.symm x)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.coe_fockEquiv_symm` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.coe_fockEquiv_symm
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.coe_fockEquiv_symm (x : lpFiniteModes Conf) :
    ((x : lpFiniteModes Conf) : Fock) = toLp (fockEquiv.symm x) := by sorry
