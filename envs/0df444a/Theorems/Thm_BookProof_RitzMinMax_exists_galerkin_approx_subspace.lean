-- Prove2me | Theorems.Thm_BookProof_RitzMinMax_exists_galerkin_approx_subspace
-- name    : BookProof.RitzMinMax.exists_galerkin_approx_subspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:36:33.267218+00:00
-- url     : https://prove2.me/theorems/09526bde-4456-4c59-9ecf-1712ab48586d
-- title:
--   (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {S : Submodule ℂ F} {k : ℕ} (hrank : Module.finrank ℂ S = k + 1) {ε : ℝ} (hε : 0 < ε) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ S' : Submodule ℂ F, S' ≤ galerkinSpan b m ∧...
-- statement:
--   Lean 4 theorem `BookProof.RitzMinMax.exists_galerkin_approx_subspace` (module `BookProof.RitzMinMax`), source chapter `BookProof/ChapterRitzMinMax.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzMinMax.lean

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.exists_galerkin_approx_subspace
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzMinMax.exists_galerkin_approx_subspace (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {S : Submodule ℂ F} {k : ℕ} (hrank : Module.finrank ℂ S = k + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ S' : Submodule ℂ F, S' ≤ galerkinSpan b m ∧
      Module.finrank ℂ S' = k + 1 ∧ rayleighSup T S' ≤ rayleighSup T S + ε := by sorry
