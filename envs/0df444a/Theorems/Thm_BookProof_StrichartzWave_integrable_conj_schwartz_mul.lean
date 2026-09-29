-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
-- name    : BookProof.StrichartzWave.integrable_conj_schwartz_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:39:09.459564+00:00
-- url     : https://prove2.me/theorems/3f28fe11-9612-4de7-a243-ea4ab7bf6876
-- title:
--   The Lean 4 theorem `integrable_conj_schwartz_mul` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integrable_conj_schwartz_mul` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.integrable_conj_schwartz_mul
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.integrable_conj_schwartz_mul (f : 𝓢(V, ℂ)) (u : Lp ℂ 2 (volume : Measure V)) :
    Integrable (fun x => (starRingEnd ℂ) (f x) * (u x)) (volume : Measure V) := by sorry
