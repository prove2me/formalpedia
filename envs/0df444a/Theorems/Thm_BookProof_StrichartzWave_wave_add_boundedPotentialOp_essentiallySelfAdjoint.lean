-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_wave_add_boundedPotentialOp_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T20:35:30.006993+00:00
-- url     : https://prove2.me/theorems/446731dc-d03e-43d0-a7a0-d3a7c3feea61
-- title:
--   `BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint` (n : ℕ) (W : SpaceTime n → ℝ) (hW : Function.HasTemperateGrowth W) (hmem : MemLp (fun x => (W x : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint` (n : ℕ) (W : SpaceTime n → ℝ) (hW : Function.HasTemperateGrowth W) (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n)) (opL2 (waveOp n 0 + potentialOp W))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveBoundedPotential
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : Function.HasTemperateGrowth W)
    (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (SpaceTime n))) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
      (opL2 (waveOp n 0 + potentialOp W)) := by sorry
