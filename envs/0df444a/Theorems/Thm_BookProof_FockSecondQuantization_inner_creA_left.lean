-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_creA_left
-- name    : BookProof.FockSecondQuantization.inner_creA_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:16:13.214483+00:00
-- url     : https://prove2.me/theorems/ba22638c-0153-41c8-8cc1-a3f3a4f21b7e
-- title:
--   (j : ℕ) (u v : FockAlg) : (inner ℂ (toLp (creA j u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (annA j v))
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_creA_left` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_creA_left
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_creA_left (j : ℕ) (u v : FockAlg) :
    (inner ℂ (toLp (creA j u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (annA j v)) := by sorry
