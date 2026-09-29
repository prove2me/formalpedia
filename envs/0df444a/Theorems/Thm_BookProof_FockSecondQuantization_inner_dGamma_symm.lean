-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_symm
-- name    : BookProof.FockSecondQuantization.inner_dGamma_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:52.882323+00:00
-- url     : https://prove2.me/theorems/13aa8b0f-4a62-4506-a462-e844dc4dd8d3
-- title:
--   {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FockAlg) : (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (dGamma col v))
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_dGamma_symm` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_dGamma_symm
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_dGamma_symm {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FockAlg) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (dGamma col v)) := by sorry
