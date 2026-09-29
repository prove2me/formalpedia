-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_ccr_creA_creA
-- name    : BookProof.FockSecondQuantization.ccr_creA_creA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:43:09.641835+00:00
-- url     : https://prove2.me/theorems/cebcd458-9268-48d7-b1ea-ad19d2fc8fd7
-- title:
--   (j k : ℕ) (u : FockAlg) : creA j (creA k u) = creA k (creA j u)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.ccr_creA_creA` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.ccr_creA_creA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.ccr_creA_creA (j k : ℕ) (u : FockAlg) : creA j (creA k u) = creA k (creA j u) := by sorry
