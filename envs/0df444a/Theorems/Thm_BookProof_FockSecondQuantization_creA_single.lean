-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_creA_single
-- name    : BookProof.FockSecondQuantization.creA_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:17:40.81497+00:00
-- url     : https://prove2.me/theorems/5cbe8040-6047-4551-8be3-3a7e2185b2d2
-- title:
--   (j : ℕ) (β : Conf) (c : ℂ) : creA j (Finsupp.single β c) = c • Finsupp.single (up j β) ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.creA_single` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.creA_single
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.creA_single (j : ℕ) (β : Conf) (c : ℂ) :
    creA j (Finsupp.single β c)
      = c • Finsupp.single (up j β) ((Real.sqrt ((β j : ℝ) + 1) : ℝ) : ℂ) := by sorry
