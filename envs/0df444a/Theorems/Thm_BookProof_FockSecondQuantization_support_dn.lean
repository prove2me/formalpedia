-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_support_dn
-- name    : BookProof.FockSecondQuantization.support_dn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:58:25.006689+00:00
-- url     : https://prove2.me/theorems/763a2826-2d4e-48ec-87ca-daeb79d06517
-- title:
--   (j : ℕ) (α : Conf) : (dn j α).support ⊆ α.support
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.support_dn` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.support_dn
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.support_dn (j : ℕ) (α : Conf) : (dn j α).support ⊆ α.support := by sorry
