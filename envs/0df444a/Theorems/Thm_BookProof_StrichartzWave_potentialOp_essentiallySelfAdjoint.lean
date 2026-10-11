-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_potentialOp_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:51:51.873922+00:00
-- url     : https://prove2.me/theorems/bcb17e9f-19eb-4e24-987b-81f53ed61fc9
-- title:
--   `BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potentialOp W))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint (W : V → ℝ) (hW : Function.HasTemperateGrowth W) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (potentialOp W)) := by sorry
