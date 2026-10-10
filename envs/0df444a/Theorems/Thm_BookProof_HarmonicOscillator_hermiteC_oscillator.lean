-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_hermiteC_oscillator
-- name    : BookProof.HarmonicOscillator.hermiteC_oscillator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:59:09.28231+00:00
-- url     : https://prove2.me/theorems/ef5fc633-2f62-4f90-a48f-c4492496bd57
-- title:
--   `BookProof.HarmonicOscillator.hermiteC_oscillator` (n : ℕ) (x : ℝ) : -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * hermiteC
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.hermiteC_oscillator` (n : ℕ) (x : ℝ) : -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * hermiteC n x
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.hermiteC_oscillator`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.hermiteC_oscillator
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.hermiteC_oscillator (n : ℕ) (x : ℝ) :
    -(deriv (deriv (hermiteC n)) x) + ((x ^ 2 / 4 : ℝ) : ℂ) * hermiteC n x
      = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * hermiteC n x := by sorry
