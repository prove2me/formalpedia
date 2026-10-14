-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_oscillatorOp_hermiteLp
-- name    : BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:12:27.020979+00:00
-- url     : https://prove2.me/theorems/aaf46a34-77a1-47e8-9d21-9e6b31c922ad
-- title:
--   `BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp` (n : ℕ) : hermiteCoreOp oscillatorSymbol ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩ = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) • hermiteLp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp` (n : ℕ) : hermiteCoreOp oscillatorSymbol ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩ = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) • hermiteLp n
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterHermiteFunctions
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteLp_mem_hermiteCore
open BookProof.HermiteCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp (n : ℕ) :
    hermiteCoreOp oscillatorSymbol ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩
      = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) • hermiteLp n := by sorry
