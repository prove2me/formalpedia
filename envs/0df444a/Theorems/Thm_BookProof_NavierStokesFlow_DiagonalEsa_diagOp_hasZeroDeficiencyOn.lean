-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiagonalEsa_diagOp_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:58:09.884994+00:00
-- url     : https://prove2.me/theorems/b0d6f45c-b268-4b70-b066-576f940d6238
-- title:
--   The Lean 4 theorem `diagOp_hasZeroDeficiencyOn` in the `ChapterNavierStokesDeficiency` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesDeficiency.lean — theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal

theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn (c : ℕ → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (diagOp c) := by sorry
