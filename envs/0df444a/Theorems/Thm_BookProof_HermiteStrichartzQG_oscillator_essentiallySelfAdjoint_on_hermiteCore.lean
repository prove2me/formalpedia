-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_oscillator_essentiallySelfAdjoint_on_hermiteCore
-- name    : BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T15:48:26.442275+00:00
-- url     : https://prove2.me/theorems/8a3771e6-16d4-455e-9206-3669041c8d25
-- title:
--   `BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore` : EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp oscillatorSymbol)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore` : EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp oscillatorSymbol)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore :
    EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp oscillatorSymbol) := by sorry
