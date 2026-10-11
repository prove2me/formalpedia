-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_symmetric
-- name    : BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:48:09.026998+00:00
-- url     : https://prove2.me/theorems/212f47a7-3896-4c81-b345-c5cf030df19e
-- title:
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric` (lam : ℕ → ℝ) : SymmetricOn hermiteCore (hermiteCoreOp lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric` (lam : ℕ → ℝ) : SymmetricOn hermiteCore (hermiteCoreOp lam)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric (lam : ℕ → ℝ) :
    SymmetricOn hermiteCore (hermiteCoreOp lam) := by sorry
