-- Prove2me | Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_eq_bandSignal_lp
-- name    : BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T16:38:05.566878+00:00
-- url     : https://prove2.me/theorems/f46fe2e3-b329-458d-859a-7afecb47b30c
-- title:
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp` (hf : BandLimited T f) (x : ℝ) : f x = bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaleyWienerSampling`.
--
--   `BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp` (hf : BandLimited T f) (x : ℝ) : f x = bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp`.

-- Generated from ChapterPaleyWienerSampling.lean — theorem BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp
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

theorem BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal_lp (hf : BandLimited T f) (x : ℝ) :
    f x = bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
      AddCircle T → ℂ) x := by sorry
