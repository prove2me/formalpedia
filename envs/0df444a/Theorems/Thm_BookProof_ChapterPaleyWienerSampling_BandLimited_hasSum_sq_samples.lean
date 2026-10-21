-- Prove2me | Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_hasSum_sq_samples
-- name    : BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T16:38:16.097981+00:00
-- url     : https://prove2.me/theorems/074df9ee-54cc-4d2d-80c9-14af14f0de45
-- title:
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples` (hf : BandLimited T f) : HasSum (fun n : ℤ => ‖f ((n : ℝ) / T)‖ ^ 2) (T * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaleyWienerSampling`.
--
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples` (hf : BandLimited T f) : HasSum (fun n : ℤ => ‖f ((n : ℝ) / T)‖ ^ 2) (T * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples`.

-- Generated from ChapterPaleyWienerSampling.lean — theorem BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling
open BookProof.ChapterPaleyWienerSampling
open BookProof.ChapterPaleyWienerSampling



open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)

variable {T : ℝ} {f g : ℝ → ℂ}
variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

theorem BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples (hf : BandLimited T f) :
    HasSum (fun n : ℤ => ‖f ((n : ℝ) / T)‖ ^ 2) (T * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) := by sorry
