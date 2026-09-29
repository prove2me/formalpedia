-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.constCoeffOp_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:44:26.490416+00:00
-- url     : https://prove2.me/theorems/d5349104-71e4-4610-a002-3c2da39edc79
-- title:
--   The Lean 4 theorem `constCoeffOp_essentiallySelfAdjoint` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `constCoeffOp_essentiallySelfAdjoint` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.constCoeffOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.constCoeffOp_essentiallySelfAdjoint (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
      (opL2 (constCoeffOp c w κ)) := by sorry
