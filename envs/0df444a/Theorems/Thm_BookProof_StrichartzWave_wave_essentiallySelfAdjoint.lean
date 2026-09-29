-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.wave_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:44:26.187441+00:00
-- url     : https://prove2.me/theorems/7eb2db82-ff6d-43b7-97dd-f748782dcb7d
-- title:
--   The Lean 4 theorem `wave_essentiallySelfAdjoint` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_essentiallySelfAdjoint` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.wave_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.wave_essentiallySelfAdjoint (n : ℕ) (κ : ℝ) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n κ)) := by sorry
