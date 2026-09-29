-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_symmetric
-- name    : BookProof.StrichartzWave.wave_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:43:38.12025+00:00
-- url     : https://prove2.me/theorems/3d3dd653-a5db-4f7a-b865-37f71973031b
-- title:
--   The Lean 4 theorem `wave_symmetric` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_symmetric` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.wave_symmetric
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.wave_symmetric (n : ℕ) (κ : ℝ) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n κ)) := by sorry
