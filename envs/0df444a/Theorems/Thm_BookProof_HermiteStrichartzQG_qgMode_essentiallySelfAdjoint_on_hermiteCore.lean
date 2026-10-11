-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_qgMode_essentiallySelfAdjoint_on_hermiteCore
-- name    : BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:02:32.585985+00:00
-- url     : https://prove2.me/theorems/4e38c16d-d057-4c28-a786-e8d590d3a3f0
-- title:
--   `BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore` (a b V : ℕ → ℝ) : EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp (qgModeSymbol a b V))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore` (a b V : ℕ → ℝ) : EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp (qgModeSymbol a b V))
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore (a b V : ℕ → ℝ) :
    EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp (qgModeSymbol a b V)) := by sorry
