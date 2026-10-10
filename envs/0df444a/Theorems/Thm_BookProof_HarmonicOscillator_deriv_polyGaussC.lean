-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_deriv_polyGaussC
-- name    : BookProof.HarmonicOscillator.deriv_polyGaussC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:58:36.333152+00:00
-- url     : https://prove2.me/theorems/612836f7-adb0-4ada-aba8-fc58d0b17049
-- title:
--   `BookProof.HarmonicOscillator.deriv_polyGaussC` (p : Polynomial ℝ) : deriv (polyGaussC p) = polyGaussC (derivative p - C (1 / 2 : ℝ) * (X * p))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.deriv_polyGaussC` (p : Polynomial ℝ) : deriv (polyGaussC p) = polyGaussC (derivative p - C (1 / 2 : ℝ) * (X * p))
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.deriv_polyGaussC`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.deriv_polyGaussC
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.deriv_polyGaussC (p : Polynomial ℝ) :
    deriv (polyGaussC p) = polyGaussC (derivative p - C (1 / 2 : ℝ) * (X * p)) := by sorry
