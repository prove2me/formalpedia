-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_harmonicOsc_essentiallySelfAdjoint
-- name    : BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:59:24.595835+00:00
-- url     : https://prove2.me/theorems/fd51de6a-c9f4-4146-bd77-110fda488d29
-- title:
--   `BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint` : EssentiallySelfAdjointOn hermiteCore harmonicOscOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint` : EssentiallySelfAdjointOn hermiteCore harmonicOscOp
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn hermiteCore harmonicOscOp := by sorry
