-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_annA_eq_zero_of_not_mem_modes
-- name    : BookProof.FockSecondQuantization.annA_eq_zero_of_not_mem_modes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:38:12.06695+00:00
-- url     : https://prove2.me/theorems/0a7d0c90-c2c3-47ea-9d78-6e57db21b01a
-- title:
--   {u : FockAlg} {k : ℕ} (h : k ∉ modes u) : annA k u = 0
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.annA_eq_zero_of_not_mem_modes` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.annA_eq_zero_of_not_mem_modes
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.annA_eq_zero_of_not_mem_modes {u : FockAlg} {k : ℕ} (h : k ∉ modes u) :
    annA k u = 0 := by sorry
