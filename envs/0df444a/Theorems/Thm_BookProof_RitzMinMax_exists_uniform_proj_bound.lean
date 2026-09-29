-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_exists_uniform_proj_bound
-- name    : BookProof.RitzMinMax.exists_uniform_proj_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:26:49.697021+00:00
-- url     : https://prove2.me/theorems/6467a6e5-9bf5-42d1-b5bf-58eda2784839
-- title:
--   (b : HilbertBasis ℕ ℂ F) (S : Submodule ℂ F) [FiniteDimensional ℂ S] {ε : ℝ} (hε : 0 < ε) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ S, ‖(galerkinSpan b m).starProjection x - x‖ ≤ ε * ‖x‖
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.exists_uniform_proj_bound` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.exists_uniform_proj_bound
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.exists_uniform_proj_bound (b : HilbertBasis ℕ ℂ F) (S : Submodule ℂ F)
    [FiniteDimensional ℂ S] {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ S,
      ‖(galerkinSpan b m).starProjection x - x‖ ≤ ε * ‖x‖ := by sorry
