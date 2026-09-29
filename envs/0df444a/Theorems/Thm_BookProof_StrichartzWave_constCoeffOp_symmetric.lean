-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_symmetric
-- name    : BookProof.StrichartzWave.constCoeffOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:42:07.50472+00:00
-- url     : https://prove2.me/theorems/b7274d12-87fe-49f8-93a7-18d90f383a16
-- title:
--   The Lean 4 theorem `constCoeffOp_symmetric` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `constCoeffOp_symmetric` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.constCoeffOp_symmetric
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.constCoeffOp_symmetric (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (constCoeffOp c w κ)) := by sorry
