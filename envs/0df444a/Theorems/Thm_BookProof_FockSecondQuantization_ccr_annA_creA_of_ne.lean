-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_creA_of_ne
-- name    : BookProof.FockSecondQuantization.ccr_annA_creA_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:42:13.305517+00:00
-- url     : https://prove2.me/theorems/010e81aa-1b2c-445a-8b51-8a7481195966
-- title:
--   {j k : ℕ} (h : j ≠ k) (u : FockAlg) : annA j (creA k u) = creA k (annA j u)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.ccr_annA_creA_of_ne` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.ccr_annA_creA_of_ne
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.ccr_annA_creA_of_ne {j k : ℕ} (h : j ≠ k) (u : FockAlg) :
    annA j (creA k u) = creA k (annA j u) := by sorry
