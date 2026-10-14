-- Prove2me | Theorems.Thm_BookProof_HarmonicOscillator_harmonicOscOp_hermiteLp
-- name    : BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:10.474775+00:00
-- url     : https://prove2.me/theorems/3d6197ae-9aa2-47f9-821f-5a7f261b0428
-- title:
--   `BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp` (n : ℕ) : harmonicOscOp ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩ = ((harmonicSymbol n : ℂ)) • hermiteLp n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHarmonicOscillatorEsa`.
--
--   `BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp` (n : ℕ) : harmonicOscOp ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩ = ((harmonicSymbol n : ℂ)) • hermiteLp n
--
--   Formalization note: Lean 4 identifier `BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp`.

-- Generated from ChapterHarmonicOscillatorEsa.lean — theorem BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Definitions.Def_ChapterHermiteFunctions
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteLp_mem_hermiteCore
open BookProof.HermiteCore
open BookProof.HarmonicOscillator



open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

theorem BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp (n : ℕ) :
    harmonicOscOp ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩
      = ((harmonicSymbol n : ℂ)) • hermiteLp n := by sorry
