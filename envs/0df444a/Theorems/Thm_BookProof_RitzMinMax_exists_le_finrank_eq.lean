-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_exists_le_finrank_eq
-- name    : BookProof.RitzMinMax.exists_le_finrank_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:26:03.445209+00:00
-- url     : https://prove2.me/theorems/f9116e63-df54-442b-9845-db28e2eea613
-- title:
--   {S : Submodule ℂ F} [FiniteDimensional ℂ S] {n : ℕ} (hn : n ≤ Module.finrank ℂ S) : ∃ S₀ : Submodule ℂ F, S₀ ≤ S ∧ Module.finrank ℂ S₀ = n
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.exists_le_finrank_eq` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.exists_le_finrank_eq
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.exists_le_finrank_eq {S : Submodule ℂ F} [FiniteDimensional ℂ S] {n : ℕ}
    (hn : n ≤ Module.finrank ℂ S) :
    ∃ S₀ : Submodule ℂ F, S₀ ≤ S ∧ Module.finrank ℂ S₀ = n := by sorry
