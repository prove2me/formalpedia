-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteDiagOp_symmetric
-- name    : BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:47:58.48712+00:00
-- url     : https://prove2.me/theorems/46307221-69ef-484d-90e5-4c2cc2de741c
-- title:
--   `BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric` (lam : ℕ → ℝ) : SymmetricOn (hermiteDiagDomain lam) (hermiteDiagOp lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric` (lam : ℕ → ℝ) : SymmetricOn (hermiteDiagDomain lam) (hermiteDiagOp lam)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.hermiteDiagOp_symmetric (lam : ℕ → ℝ) :
    SymmetricOn (hermiteDiagDomain lam) (hermiteDiagOp lam) := by sorry
