-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_nonneg
-- name    : BookProof.FockSecondQuantization.inner_dGamma_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:33.95148+00:00
-- url     : https://prove2.me/theorems/cb055932-6ff9-4456-8ccf-b9abea6a5f3d
-- title:
--   {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FockAlg) : 0 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_dGamma_nonneg` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_dGamma_nonneg
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_dGamma_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FockAlg) :
    0 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by sorry
