-- Prove2me | Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_integrable_fourier
-- name    : BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T16:38:04.732618+00:00
-- url     : https://prove2.me/theorems/3e3fa14c-a27c-41be-8912-d213c16b2aca
-- title:
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier` (hf : BandLimited T f) : Integrable (𝓕 f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaleyWienerSampling`.
--
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier` (hf : BandLimited T f) : Integrable (𝓕 f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier`.

-- Generated from ChapterPaleyWienerSampling.lean — theorem BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier
import Definitions.Def_ChapterShannonSampling
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
open BookProof.ChapterPaleyWienerSampling
open BookProof.ChapterPaleyWienerSampling



open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)

variable {T : ℝ} {f g : ℝ → ℂ}

theorem BookProof.ChapterPaleyWienerSampling.BandLimited.integrable_fourier (hf : BandLimited T f) : Integrable (𝓕 f) := by sorry
