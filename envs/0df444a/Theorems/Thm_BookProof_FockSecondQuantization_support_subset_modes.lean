-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_support_subset_modes
-- name    : BookProof.FockSecondQuantization.support_subset_modes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:23:25.775089+00:00
-- url     : https://prove2.me/theorems/53dbf4c1-2c4d-4243-b0c8-08704c5e497e
-- title:
--   {u : FockAlg} {β : Conf} (h : β ∈ u.support) : β.support ⊆ modes u
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.support_subset_modes` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.support_subset_modes
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.support_subset_modes {u : FockAlg} {β : Conf} (h : β ∈ u.support) :
    β.support ⊆ modes u := by sorry
