-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_harmonicOsc_not_bounded
-- name    : BookProof.HarmonicOscillator.harmonicOsc_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:00:00.037388+00:00
-- url     : https://prove2.me/theorems/6ef4528a-2bd1-4a02-bb7e-cbea1aa78351
-- title:
--   `BookProof.HarmonicOscillator.harmonicOsc_not_bounded` : ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖harmonicOscOp f‖ ≤ C * ‖(f : L2R)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.harmonicOsc_not_bounded` : ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖harmonicOscOp f‖ ≤ C * ‖(f : L2R)‖
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.harmonicOsc_not_bounded`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.harmonicOsc_not_bounded
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.harmonicOsc_not_bounded :
    ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖harmonicOscOp f‖ ≤ C * ‖(f : L2R)‖ := by sorry
