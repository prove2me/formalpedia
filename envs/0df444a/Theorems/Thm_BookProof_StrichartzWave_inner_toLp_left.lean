-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
-- name    : BookProof.StrichartzWave.inner_toLp_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:38:58.640887+00:00
-- url     : https://prove2.me/theorems/3faf8274-c257-43aa-93dc-0b374cfd1eb4
-- title:
--   The Lean 4 theorem `inner_toLp_left` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_toLp_left` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.inner_toLp_left
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.inner_toLp_left (f : 𝓢(V, ℂ)) (u : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (f.toLp 2 (volume : Measure V)) u : ℂ)
      = ∫ x, (starRingEnd ℂ) (f x) * (u x) := by sorry
