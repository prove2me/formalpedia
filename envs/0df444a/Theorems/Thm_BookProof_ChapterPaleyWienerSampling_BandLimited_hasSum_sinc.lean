-- Prove2me | Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_hasSum_sinc
-- name    : BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T16:38:07.62992+00:00
-- url     : https://prove2.me/theorems/6827174d-ae91-4f4a-9126-c0ef44a831a9
-- title:
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc` (hf : BandLimited T f) (x : ℝ) : HasSum (fun n : ℤ => f ((n : ℝ) / T) * (sinc (T * x - n) : ℝ)) (f x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaleyWienerSampling`.
--
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc` (hf : BandLimited T f) (x : ℝ) : HasSum (fun n : ℤ => f ((n : ℝ) / T) * (sinc (T * x - n) : ℝ)) (f x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc`.

-- Generated from ChapterPaleyWienerSampling.lean — theorem BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc
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

theorem BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sinc (hf : BandLimited T f) (x : ℝ) :
    HasSum (fun n : ℤ => f ((n : ℝ) / T) * (sinc (T * x - n) : ℝ)) (f x) := by sorry
