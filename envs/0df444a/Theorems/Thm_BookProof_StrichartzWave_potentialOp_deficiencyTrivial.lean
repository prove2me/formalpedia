-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_potentialOp_deficiencyTrivial
-- name    : BookProof.StrichartzWave.potentialOp_deficiencyTrivial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:52:40.530924+00:00
-- url     : https://prove2.me/theorems/c00bea1d-1409-48b1-87f3-692b5629cb51
-- title:
--   `BookProof.StrichartzWave.potentialOp_deficiencyTrivial` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) {z : ℂ} (hz : z.im ≠ 0) : BookProof.FarisLavine.DeficiencyTrivialAt (schwa
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.potentialOp_deficiencyTrivial` (W : V → ℝ) (hW : Function.HasTemperateGrowth W) {z : ℂ} (hz : z.im ≠ 0) : BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 (potentialOp W)) z
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.potentialOp_deficiencyTrivial`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.potentialOp_deficiencyTrivial
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.potentialOp_deficiencyTrivial (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    {z : ℂ} (hz : z.im ≠ 0) :
    BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 (potentialOp W)) z := by sorry
