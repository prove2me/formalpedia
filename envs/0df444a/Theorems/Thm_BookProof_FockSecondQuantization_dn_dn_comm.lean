-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dn_dn_comm
-- name    : BookProof.FockSecondQuantization.dn_dn_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:57:40.622385+00:00
-- url     : https://prove2.me/theorems/1df9cb2f-5bb1-40fb-9ed4-75d39320a835
-- title:
--   (j k : ℕ) (α : Conf) : dn k (dn j α) = dn j (dn k α)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dn_dn_comm` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dn_dn_comm
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dn_dn_comm (j k : ℕ) (α : Conf) : dn k (dn j α) = dn j (dn k α) := by sorry
