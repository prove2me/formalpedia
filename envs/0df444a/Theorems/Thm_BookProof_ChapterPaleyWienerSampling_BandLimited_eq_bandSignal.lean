-- Prove2me | Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_eq_bandSignal
-- name    : BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T16:37:59.596995+00:00
-- url     : https://prove2.me/theorems/8327bc10-7c72-4e76-ad52-ef1b023bb031
-- title:
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal` (hf : BandLimited T f) (x : ℝ) : f x = bandSignal (T := T) (bandSpectrum T f) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaleyWienerSampling`.
--
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal` (hf : BandLimited T f) (x : ℝ) : f x = bandSignal (T := T) (bandSpectrum T f) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal`.

-- Generated from ChapterPaleyWienerSampling.lean — theorem BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal
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

theorem BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal (hf : BandLimited T f) (x : ℝ) :
    f x = bandSignal (T := T) (bandSpectrum T f) x := by sorry
