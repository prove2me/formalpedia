-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dn_self
-- name    : BookProof.FockSecondQuantization.dn_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:19:50.341795+00:00
-- url     : https://prove2.me/theorems/45ee5811-983b-4b73-9090-e464b27c7752
-- title:
--   (j : ℕ) (α : Conf) : dn j α j = α j - 1
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dn_self` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dn_self
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dn_self (j : ℕ) (α : Conf) : dn j α j = α j - 1 := by sorry
