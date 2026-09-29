-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_up_dn_comm
-- name    : BookProof.FockSecondQuantization.up_dn_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:02:07.601596+00:00
-- url     : https://prove2.me/theorems/84b0f8ab-5c95-447b-95f6-57c6e551549f
-- title:
--   {j k : ℕ} (h : j ≠ k) (α : Conf) : dn k (up j α) = up j (dn k α)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.up_dn_comm` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.up_dn_comm
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.up_dn_comm {j k : ℕ} (h : j ≠ k) (α : Conf) : dn k (up j α) = up j (dn k α) := by sorry
