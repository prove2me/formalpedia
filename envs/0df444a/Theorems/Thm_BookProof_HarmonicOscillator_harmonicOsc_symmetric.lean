-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_harmonicOsc_symmetric
-- name    : BookProof.HarmonicOscillator.harmonicOsc_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:58:55.582401+00:00
-- url     : https://prove2.me/theorems/7c6b5afa-f576-491d-afbe-1c242ca10262
-- title:
--   `BookProof.HarmonicOscillator.harmonicOsc_symmetric` : SymmetricOn hermiteCore harmonicOscOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.harmonicOsc_symmetric` : SymmetricOn hermiteCore harmonicOscOp
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.harmonicOsc_symmetric`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.harmonicOsc_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.harmonicOsc_symmetric : SymmetricOn hermiteCore harmonicOscOp := by sorry
