-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_annA_single
-- name    : BookProof.FockSecondQuantization.annA_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:14:16.917461+00:00
-- url     : https://prove2.me/theorems/2c360bf0-262d-4556-a843-5d1e943a1d5b
-- title:
--   (j : ℕ) (β : Conf) (c : ℂ) : annA j (Finsupp.single β c) = c • Finsupp.single (dn j β) ((Real.sqrt (β j) : ℝ) : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.annA_single` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.annA_single
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.annA_single (j : ℕ) (β : Conf) (c : ℂ) :
    annA j (Finsupp.single β c) = c • Finsupp.single (dn j β) ((Real.sqrt (β j) : ℝ) : ℂ) := by sorry
