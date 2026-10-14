-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_potentialOp_symmetric
-- name    : BookProof.StrichartzWave.potentialOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:53:23.803984+00:00
-- url     : https://prove2.me/theorems/06eb16b6-ec92-44b6-a954-6becc7f903b4
-- title:
--   `BookProof.StrichartzWave.potentialOp_symmetric` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (potentialOp W))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.potentialOp_symmetric` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) : BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (potentialOp W))
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.potentialOp_symmetric`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.potentialOp_symmetric
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.potentialOp_symmetric (W : V → ℝ) (hW : Function.HasTemperateGrowth W) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 (potentialOp W)) := by sorry
