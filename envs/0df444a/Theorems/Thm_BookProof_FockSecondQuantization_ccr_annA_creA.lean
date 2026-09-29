-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA
-- name    : BookProof.FockSecondQuantization.ccr_annA_creA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:41:31.789347+00:00
-- url     : https://prove2.me/theorems/12c51742-c5dc-4a9c-bf1c-e497d5aec52d
-- title:
--   (j : ℕ) (u : FockAlg) : annA j (creA j u) - creA j (annA j u) = u
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.ccr_annA_creA` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.ccr_annA_creA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.ccr_annA_creA (j : ℕ) (u : FockAlg) : annA j (creA j u) - creA j (annA j u) = u := by sorry
