-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_galerkin_model_gap_eventually_pos
-- name    : BookProof.RitzPerturbation.galerkin_model_gap_eventually_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:37:30.451034+00:00
-- url     : https://prove2.me/theorems/68b94700-8322-4856-ac8e-efb48b5ead5c
-- title:
--   (T T' : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {eps : ℝ} (hd : ‖T - T'‖ ≤ eps) (hgap : 2 * eps < minmaxGap T) : ∀ᶠ m : ℕ in atTop, 0 < minmaxLevelIn T' (galerkinSpan b m) 1 - minmaxLevelIn T'...
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.galerkin_model_gap_eventually_pos` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.galerkin_model_gap_eventually_pos
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.galerkin_model_gap_eventually_pos (T T' : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {eps : ℝ} (hd : ‖T - T'‖ ≤ eps) (hgap : 2 * eps < minmaxGap T) :
    ∀ᶠ m : ℕ in atTop, 0 < minmaxLevelIn T' (galerkinSpan b m) 1
      - minmaxLevelIn T' (galerkinSpan b m) 0 := by sorry
