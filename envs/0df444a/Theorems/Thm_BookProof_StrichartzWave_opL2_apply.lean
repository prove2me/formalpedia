-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_opL2_apply
-- name    : BookProof.StrichartzWave.opL2_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:39:27.334832+00:00
-- url     : https://prove2.me/theorems/e87134fc-83d5-46a1-b50e-a22e446c9aeb
-- title:
--   The Lean 4 theorem `opL2_apply` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `opL2_apply` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.opL2_apply
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.opL2_apply (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (f : 𝓢(V, ℂ)) :
    opL2 T (schwartzEquiv V f) = (T f).toLp 2 (volume : Measure V) := by sorry
