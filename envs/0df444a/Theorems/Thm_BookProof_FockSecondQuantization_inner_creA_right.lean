-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_right
-- name    : BookProof.FockSecondQuantization.inner_creA_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:15:37.321992+00:00
-- url     : https://prove2.me/theorems/ef7135cf-2a3a-4a6d-a3fc-e9117930ee17
-- title:
--   (j : ℕ) (u v : FockAlg) : (inner ℂ (toLp u) (toLp (creA j v)) : ℂ) = inner ℂ (toLp (annA j u)) (toLp v)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_creA_right` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_creA_right
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_creA_right (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp (creA j v)) : ℂ) = inner ℂ (toLp (annA j u)) (toLp v) := by sorry
