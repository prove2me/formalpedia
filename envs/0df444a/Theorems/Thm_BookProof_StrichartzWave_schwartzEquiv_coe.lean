-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
-- name    : BookProof.StrichartzWave.schwartzEquiv_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:39:30.935184+00:00
-- url     : https://prove2.me/theorems/c465e5b2-9a9c-4714-9cf3-a1a2a8989882
-- title:
--   The Lean 4 theorem `schwartzEquiv_coe` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `schwartzEquiv_coe` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.schwartzEquiv_coe
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.schwartzEquiv_coe (f : 𝓢(V, ℂ)) :
    ((schwartzEquiv V f : schwartzDomain V) : Lp ℂ 2 (volume : Measure V))
      = f.toLp 2 (volume : Measure V) := by sorry
