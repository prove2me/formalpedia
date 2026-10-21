-- Prove2me | Theorems.Thm_BookProof_ChapterPaleyWienerSampling_bandSignal_bandSpectrumLp
-- name    : BookProof.ChapterPaleyWienerSampling.bandSignal_bandSpectrumLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T16:37:53.83417+00:00
-- url     : https://prove2.me/theorems/b18249e3-dcb0-4298-804e-f6676f637719
-- title:
--   `BookProof.ChapterPaleyWienerSampling.bandSignal_bandSpectrumLp` (hf : BandLimited T f) (x : ℝ) : bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaleyWienerSampling`.
--
--   `BookProof.ChapterPaleyWienerSampling.bandSignal_bandSpectrumLp` (hf : BandLimited T f) (x : ℝ) : bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ) x = bandSignal (T := T) (bandSpectrum T f) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPaleyWienerSampling.bandSignal_bandSpectrumLp`.

-- Generated from ChapterPaleyWienerSampling.lean — theorem BookProof.ChapterPaleyWienerSampling.bandSignal_bandSpectrumLp
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling
open BookProof.ChapterPaleyWienerSampling



open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)

variable {T : ℝ} {f g : ℝ → ℂ}
variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

theorem BookProof.ChapterPaleyWienerSampling.bandSignal_bandSpectrumLp (hf : BandLimited T f) (x : ℝ) :
    bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
        AddCircle T → ℂ) x
      = bandSignal (T := T) (bandSpectrum T f) x := by sorry
