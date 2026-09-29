-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_ccr_annA_annA
-- name    : BookProof.FockSecondQuantization.ccr_annA_annA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:39:23.75253+00:00
-- url     : https://prove2.me/theorems/cd1a367b-ea78-444a-8c64-07e0899c515d
-- title:
--   (j k : ℕ) (u : FockAlg) : annA j (annA k u) = annA k (annA j u)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.ccr_annA_annA` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.ccr_annA_annA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.ccr_annA_annA (j k : ℕ) (u : FockAlg) : annA j (annA k u) = annA k (annA j u) := by sorry
