-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_multiplierOp_symmetric
-- name    : BookProof.StrichartzWave.multiplierOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:08.416704+00:00
-- url     : https://prove2.me/theorems/0e37b50d-d0f2-4968-a69c-1788711a6e8f
-- title:
--   `BookProof.StrichartzWave.multiplierOp_symmetric` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (multiplierOp m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.multiplierOp_symmetric` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (multiplierOp m))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.multiplierOp_symmetric`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.multiplierOp_symmetric
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.multiplierOp_symmetric (m : V → ℝ) (hm : Function.HasTemperateGrowth m) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (multiplierOp m)) := by sorry
