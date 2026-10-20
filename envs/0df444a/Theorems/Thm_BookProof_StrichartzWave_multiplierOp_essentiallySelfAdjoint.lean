-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_multiplierOp_essentiallySelfAdjoint
-- name    : BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:54.640824+00:00
-- url     : https://prove2.me/theorems/e979e640-8a72-4ee5-b2a1-c9c097c61664
-- title:
--   `BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) : BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (multiplierOp m))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint (m : V → ℝ) (hm : Function.HasTemperateGrowth m) :
    BookProof.FarisLavine.EssentiallySelfAdjointOn (schwartzDomain V) (opL2 (multiplierOp m)) := by sorry
