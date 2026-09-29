-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_support_creA
-- name    : BookProof.FockSecondQuantization.support_creA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:43:47.378588+00:00
-- url     : https://prove2.me/theorems/274ae452-e1c5-4925-a6c8-d095db218037
-- title:
--   (j : ℕ) (u : FockAlg) : (creA j u).support ⊆ u.support.image (up j)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.support_creA` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.support_creA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.support_creA (j : ℕ) (u : FockAlg) : (creA j u).support ⊆ u.support.image (up j) := by sorry
