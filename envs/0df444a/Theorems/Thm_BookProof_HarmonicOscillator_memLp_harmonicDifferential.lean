-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_memLp_harmonicDifferential
-- name    : BookProof.HarmonicOscillator.memLp_harmonicDifferential
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:59:15.371983+00:00
-- url     : https://prove2.me/theorems/f2633558-0b35-4844-99f9-6db7f253050b
-- title:
--   `BookProof.HarmonicOscillator.memLp_harmonicDifferential` (n : ℕ) : MemLp (fun x : ℝ => -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x) 2 (volume : Measure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.memLp_harmonicDifferential` (n : ℕ) : MemLp (fun x : ℝ => -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x) 2 (volume : Measure ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.memLp_harmonicDifferential`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.memLp_harmonicDifferential
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.memLp_harmonicDifferential (n : ℕ) :
    MemLp (fun x : ℝ => -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x)
      2 (volume : Measure ℝ) := by sorry
