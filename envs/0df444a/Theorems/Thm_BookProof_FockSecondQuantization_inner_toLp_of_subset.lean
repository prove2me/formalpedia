-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
-- name    : BookProof.FockSecondQuantization.inner_toLp_of_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:21:17.6899+00:00
-- url     : https://prove2.me/theorems/45cf1c3c-a7fe-406b-8d9a-ce5b48673012
-- title:
--   {u : FockAlg} {s : Finset Conf} (hs : u.support ⊆ s) (v : FockAlg) : (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ s, (starRingEnd ℂ) (u α) * v α
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_toLp_of_subset` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_toLp_of_subset
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_toLp_of_subset {u : FockAlg} {s : Finset Conf} (hs : u.support ⊆ s)
    (v : FockAlg) :
    (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ s, (starRingEnd ℂ) (u α) * v α := by sorry
