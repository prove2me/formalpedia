-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_hermiteLp
-- name    : BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:12:45.47498+00:00
-- url     : https://prove2.me/theorems/18da469f-60ad-402f-9c01-5b65cedc6d52
-- title:
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp` (lam : ℕ → ℝ) (n : ℕ) : hermiteCoreOp lam ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩ = ((lam n : ℂ)) • hermiteLp n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp` (lam : ℕ → ℝ) (n : ℕ) : hermiteCoreOp lam ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩ = ((lam n : ℂ)) • hermiteLp n
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteLp_mem_hermiteCore
open BookProof.FarisLavine
open BookProof.HermiteCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp (lam : ℕ → ℝ) (n : ℕ) :
    hermiteCoreOp lam ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩
      = ((lam n : ℂ)) • hermiteLp n := by sorry
