-- Prove2me | Theorems.Thm_BookProof_RitzPerturbation_galerkin_model_gap_tendsto
-- name    : BookProof.RitzPerturbation.galerkin_model_gap_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:38:14.154079+00:00
-- url     : https://prove2.me/theorems/cb26c22f-2abe-4b65-9e75-d99b8573d3b8
-- title:
--   (T T' : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {eps : ℝ} (hd : ‖T - T'‖ ≤ eps) : Tendsto (fun m : ℕ => minmaxLevelIn T' (galerkinSpan b m) 1 - minmaxLevelIn T' (galerkinSpan b m) 0) atTop (𝓝...
-- statement:
--   Lean 4 theorem `BookProof.RitzPerturbation.galerkin_model_gap_tendsto` (module `BookProof.RitzPerturbation`), source chapter `BookProof/ChapterRitzPerturbation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterRitzPerturbation.lean

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.galerkin_model_gap_tendsto
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.RitzPerturbation.galerkin_model_gap_tendsto (T T' : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {eps : ℝ}
    (hd : ‖T - T'‖ ≤ eps) :
    Tendsto (fun m : ℕ => minmaxLevelIn T' (galerkinSpan b m) 1
        - minmaxLevelIn T' (galerkinSpan b m) 0) atTop (𝓝 (minmaxGap T')) ∧
      |minmaxGap T' - minmaxGap T| ≤ 2 * eps := by sorry
