-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_essentiallySelfAdjoint
-- name    : BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:47:57.706322+00:00
-- url     : https://prove2.me/theorems/7fdad987-9103-4e9c-bf5c-c55745b3aabc
-- title:
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint` (lam : ℕ → ℝ) : EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint` (lam : ℕ → ℝ) : EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp lam)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint (lam : ℕ → ℝ) :
    EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp lam) := by sorry
