-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_hasDerivAt_polyGaussC
-- name    : BookProof.HarmonicOscillator.hasDerivAt_polyGaussC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:58:22.902837+00:00
-- url     : https://prove2.me/theorems/54d2e299-85d6-4674-a5c3-a7ed3a7f36c0
-- title:
--   `BookProof.HarmonicOscillator.hasDerivAt_polyGaussC` (p : Polynomial ℝ) (x : ℝ) : HasDerivAt (polyGaussC p) ((((derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x : ℝ) : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.hasDerivAt_polyGaussC` (p : Polynomial ℝ) (x : ℝ) : HasDerivAt (polyGaussC p) ((((derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x : ℝ) : ℂ)) x
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.hasDerivAt_polyGaussC`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.hasDerivAt_polyGaussC
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.hasDerivAt_polyGaussC (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (polyGaussC p)
      ((((derivative p - C (1 / 2 : ℝ) * (X * p)).eval x * gaussH x : ℝ) : ℂ)) x := by sorry
