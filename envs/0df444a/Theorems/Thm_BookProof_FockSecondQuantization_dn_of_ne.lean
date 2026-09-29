-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dn_of_ne
-- name    : BookProof.FockSecondQuantization.dn_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:19:06.154375+00:00
-- url     : https://prove2.me/theorems/733be9e6-fbef-4664-8413-6a664a4713e8
-- title:
--   {i j : ℕ} (α : Conf) (h : i ≠ j) : dn j α i = α i
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dn_of_ne` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dn_of_ne
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dn_of_ne {i j : ℕ} (α : Conf) (h : i ≠ j) : dn j α i = α i := by sorry
